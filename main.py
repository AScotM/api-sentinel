import argparse
import base64
import concurrent.futures
import csv
import dataclasses
import datetime
import email.utils
import hashlib
import http.client
import ipaddress
import json
import math
import os
import random
import re
import signal
import socket
import sqlite3
import ssl
import statistics
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

VERSION = "1.0.0"
SAFE_METHODS = {"GET", "HEAD"}
METHODS = {"GET", "HEAD", "POST", "PUT", "PATCH", "DELETE", "OPTIONS"}
STOP = threading.Event()
SENSITIVE = {"authorization", "proxy-authorization", "cookie", "set-cookie", "x-api-key"}


class SentinelError(Exception):
    pass


@dataclass
class Endpoint:
    name: str
    url: str
    method: str = "GET"
    headers: dict = field(default_factory=dict)
    body: Optional[str] = None
    timeout: float = 10.0
    expected_status: list = field(default_factory=lambda: [200])
    expected_headers: dict = field(default_factory=dict)
    expected_text: Optional[str] = None
    expected_json: dict = field(default_factory=dict)
    max_latency_ms: Optional[float] = None
    retries: int = 0
    retry_backoff: float = 0.5
    verify_tls: bool = True
    allow_mutation: bool = False
    max_bytes: int = 1048576
    tags: list = field(default_factory=list)

    @classmethod
    def from_dict(cls, obj):
        if not isinstance(obj, dict):
            raise SentinelError("Endpoint must be an object")
        fields = {f.name for f in dataclasses.fields(cls)}
        unknown = set(obj) - fields
        if unknown:
            raise SentinelError("Unknown endpoint fields: " + ", ".join(sorted(unknown)))
        item = cls(**obj)
        item.validate()
        return item

    def validate(self):
        if not self.name or not isinstance(self.name, str):
            raise SentinelError("Endpoint name must be a nonempty string")
        parsed = urllib.parse.urlsplit(self.url)
        if parsed.scheme not in {"http", "https"} or not parsed.hostname:
            raise SentinelError(f"Invalid HTTP URL for {self.name}")
        if parsed.username or parsed.password:
            raise SentinelError("Credentials in URLs are not supported")
        if not isinstance(self.method, str):
            raise SentinelError("Invalid method")
        self.method = self.method.upper()
        if self.method not in METHODS:
            raise SentinelError(f"Unsupported method {self.method}")
        if self.method not in SAFE_METHODS and not self.allow_mutation:
            raise SentinelError(f"{self.name}: {self.method} requires allow_mutation=true")
        if not 0 < self.timeout <= 300:
            raise SentinelError("Timeout must be between 0 and 300 seconds")
        if not 0 <= self.retries <= 10:
            raise SentinelError("Retries must be between 0 and 10")
        if not 0 <= self.retry_backoff <= 60:
            raise SentinelError("Invalid retry backoff")
        if not 1 <= self.max_bytes <= 50_000_000:
            raise SentinelError("Invalid max_bytes")
        if not isinstance(self.expected_status, list) or not self.expected_status:
            raise SentinelError("expected_status must be a nonempty list")
        if any(not isinstance(s, int) or not 100 <= s <= 599 for s in self.expected_status):
            raise SentinelError("Invalid expected status")
        if not isinstance(self.headers, dict) or not isinstance(self.expected_headers, dict):
            raise SentinelError("Headers must be objects")
        if not isinstance(self.expected_json, dict):
            raise SentinelError("expected_json must be an object")
        for key, value in self.headers.items():
            if not isinstance(key, str) or not isinstance(value, str) or "\r" in key + value or "\n" in key + value:
                raise SentinelError("Invalid header")
        if self.body is not None and not isinstance(self.body, str):
            raise SentinelError("Body must be text")
        if self.max_latency_ms is not None and self.max_latency_ms <= 0:
            raise SentinelError("max_latency_ms must be positive")


@dataclass
class Result:
    run_id: str
    name: str
    url: str
    method: str
    timestamp: str
    success: bool
    status: Optional[int] = None
    latency_ms: float = 0.0
    bytes_read: int = 0
    attempts: int = 0
    error: Optional[str] = None
    failures: list = field(default_factory=list)
    response_headers: dict = field(default_factory=dict)
    body_sha256: Optional[str] = None
    tls: dict = field(default_factory=dict)
    tags: list = field(default_factory=list)

    def as_dict(self):
        return dataclasses.asdict(self)


def utcnow():
    return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="milliseconds")


def redact_headers(headers):
    return {k: "[REDACTED]" if k.lower() in SENSITIVE else v for k, v in headers.items()}


def normalize_url(url):
    parsed = urllib.parse.urlsplit(url)
    return urllib.parse.urlunsplit((parsed.scheme, parsed.netloc, parsed.path, parsed.query, ""))


def json_path(obj, path):
    current = obj
    for token in str(path).split("."):
        if isinstance(current, list):
            try:
                current = current[int(token)]
            except (ValueError, IndexError):
                raise KeyError(path)
        elif isinstance(current, dict) and token in current:
            current = current[token]
        else:
            raise KeyError(path)
    return current


def percentile(values, p):
    if not values:
        return None
    ordered = sorted(values)
    index = (len(ordered) - 1) * p / 100
    low = math.floor(index)
    high = math.ceil(index)
    return ordered[low] + (ordered[high] - ordered[low]) * (index - low)


def describe(values):
    if not values:
        return {"count": 0}
    return {
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "mean": statistics.fmean(values),
        "median": statistics.median(values),
        "p90": percentile(values, 90),
        "p95": percentile(values, 95),
        "p99": percentile(values, 99),
        "stddev": statistics.pstdev(values),
    }


def check_response(endpoint, status, headers, data, latency):
    failures = []
    if status not in endpoint.expected_status:
        failures.append(f"Unexpected status {status}; expected {endpoint.expected_status}")
    lower = {k.lower(): v for k, v in headers.items()}
    for key, expected in endpoint.expected_headers.items():
        actual = lower.get(key.lower())
        if actual is None or str(expected).lower() not in actual.lower():
            failures.append(f"Header {key} does not match")
    if endpoint.max_latency_ms is not None and latency > endpoint.max_latency_ms:
        failures.append(f"Latency {latency:.2f}ms exceeds {endpoint.max_latency_ms:.2f}ms")
    if endpoint.expected_text is not None:
        text = data.decode("utf-8", errors="replace")
        if endpoint.expected_text not in text:
            failures.append("Expected text not found")
    if endpoint.expected_json:
        try:
            obj = json.loads(data)
            for key, expected in endpoint.expected_json.items():
                try:
                    actual = json_path(obj, key)
                    if actual != expected:
                        failures.append(f"JSON value mismatch at {key}")
                except KeyError:
                    failures.append(f"Missing JSON path {key}")
        except (ValueError, UnicodeDecodeError):
            failures.append("Response is not valid JSON")
    return failures


def tls_inspect(host, port, timeout, verify=True):
    output = {"hostname": host, "port": port, "verified": verify}
    context = ssl.create_default_context() if verify else ssl._create_unverified_context()
    started = time.perf_counter()
    try:
        with socket.create_connection((host, port), timeout=timeout) as raw:
            with context.wrap_socket(raw, server_hostname=host) as secure:
                output["protocol"] = secure.version()
                cipher = secure.cipher()
                output["cipher"] = cipher[0] if cipher else None
                cert = secure.getpeercert()
                if cert:
                    output["subject"] = str(cert.get("subject", ""))
                    output["issuer"] = str(cert.get("issuer", ""))
                    output["not_after"] = cert.get("notAfter")
                    output["not_before"] = cert.get("notBefore")
                    output["serial_number"] = cert.get("serialNumber")
                    if cert.get("notAfter"):
                        expires = ssl.cert_time_to_seconds(cert["notAfter"])
                        output["days_remaining"] = round((expires - time.time()) / 86400, 2)
                output["handshake_ms"] = round((time.perf_counter() - started) * 1000, 3)
    except (OSError, ssl.SSLError, ValueError) as exc:
        output["error"] = str(exc)
    return output


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise urllib.error.HTTPError(req.full_url, code, "Redirect blocked", headers, fp)


def probe_once(endpoint, run_id, inspect_tls=False, follow_redirects=False):
    result = Result(run_id, endpoint.name, normalize_url(endpoint.url), endpoint.method, utcnow(), False, tags=list(endpoint.tags))
    started = time.perf_counter()
    data = endpoint.body.encode("utf-8") if endpoint.body is not None else None
    context = ssl.create_default_context() if endpoint.verify_tls else ssl._create_unverified_context()
    handlers = [urllib.request.HTTPSHandler(context=context)]
    if not follow_redirects:
        handlers.append(NoRedirect())
    opener = urllib.request.build_opener(*handlers)
    request = urllib.request.Request(endpoint.url, data=data, headers=endpoint.headers, method=endpoint.method)
    try:
        try:
            response = opener.open(request, timeout=endpoint.timeout)
        except urllib.error.HTTPError as exc:
            response = exc
        with response:
            result.status = response.status
            result.response_headers = redact_headers(dict(response.headers.items()))
            payload = response.read(endpoint.max_bytes + 1)
            if len(payload) > endpoint.max_bytes:
                result.failures.append("Response exceeds maximum body size")
                payload = payload[:endpoint.max_bytes]
            result.bytes_read = len(payload)
            result.body_sha256 = hashlib.sha256(payload).hexdigest()
            result.latency_ms = round((time.perf_counter() - started) * 1000, 3)
            result.failures.extend(check_response(endpoint, result.status, dict(response.headers.items()), payload, result.latency_ms))
    except (OSError, ValueError, TimeoutError, urllib.error.URLError) as exc:
        result.error = f"{type(exc).__name__}: {exc}"
        result.failures.append("Transport failure")
        result.latency_ms = round((time.perf_counter() - started) * 1000, 3)
    if inspect_tls and urllib.parse.urlsplit(endpoint.url).scheme == "https":
        parsed = urllib.parse.urlsplit(endpoint.url)
        result.tls = tls_inspect(parsed.hostname, parsed.port or 443, endpoint.timeout, endpoint.verify_tls)
        if result.tls.get("error"):
            result.failures.append("TLS inspection failure")
        elif result.tls.get("days_remaining") is not None and result.tls["days_remaining"] < 14:
            result.failures.append("TLS certificate expires within 14 days")
    result.success = not result.failures
    return result


def probe(endpoint, run_id, inspect_tls=False, follow_redirects=False):
    result = None
    for attempt in range(endpoint.retries + 1):
        if STOP.is_set():
            break
        result = probe_once(endpoint, run_id, inspect_tls, follow_redirects)
        result.attempts = attempt + 1
        if result.success:
            return result
        if attempt < endpoint.retries:
            STOP.wait(min(60, endpoint.retry_backoff * (2 ** attempt)))
    if result is None:
        result = Result(run_id, endpoint.name, normalize_url(endpoint.url), endpoint.method, utcnow(), False, error="Interrupted", failures=["Interrupted"])
    return result


class Database:
    def __init__(self, path):
        self.path = path
        Path(path).expanduser().parent.mkdir(parents=True, exist_ok=True)
        self.connection = sqlite3.connect(path, timeout=20)
        self.connection.execute("PRAGMA busy_timeout=20000")
        self.connection.execute("PRAGMA journal_mode=WAL")
        self.connection.execute("CREATE TABLE IF NOT EXISTS probes (id INTEGER PRIMARY KEY AUTOINCREMENT, run_id TEXT NOT NULL, name TEXT NOT NULL, url TEXT NOT NULL, method TEXT NOT NULL, timestamp TEXT NOT NULL, success INTEGER NOT NULL, status INTEGER, latency_ms REAL NOT NULL, bytes_read INTEGER NOT NULL, attempts INTEGER NOT NULL, error TEXT, failures TEXT NOT NULL, response_headers TEXT NOT NULL, body_sha256 TEXT, tls TEXT NOT NULL, tags TEXT NOT NULL)")
        self.connection.execute("CREATE INDEX IF NOT EXISTS idx_probes_name_time ON probes(name,timestamp)")
        self.connection.execute("CREATE INDEX IF NOT EXISTS idx_probes_run ON probes(run_id)")
        self.connection.commit()

    def save(self, results):
        rows = []
        for r in results:
            rows.append((r.run_id, r.name, r.url, r.method, r.timestamp, int(r.success), r.status, r.latency_ms, r.bytes_read, r.attempts, r.error, json.dumps(r.failures), json.dumps(r.response_headers), r.body_sha256, json.dumps(r.tls), json.dumps(r.tags)))
        with self.connection:
            self.connection.executemany("INSERT INTO probes(run_id,name,url,method,timestamp,success,status,latency_ms,bytes_read,attempts,error,failures,response_headers,body_sha256,tls,tags) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", rows)

    def history(self, name=None, limit=1000, since=None):
        clauses = []
        params = []
        if name:
            clauses.append("name = ?")
            params.append(name)
        if since:
            clauses.append("timestamp >= ?")
            params.append(since)
        sql = "SELECT run_id,name,url,method,timestamp,success,status,latency_ms,bytes_read,attempts,error,failures,response_headers,body_sha256,tls,tags FROM probes"
        if clauses:
            sql += " WHERE " + " AND ".join(clauses)
        sql += " ORDER BY timestamp DESC,id DESC LIMIT ?"
        params.append(limit)
        cur = self.connection.execute(sql, params)
        keys = [x[0] for x in cur.description]
        output = []
        for row in cur.fetchall():
            obj = dict(zip(keys, row))
            obj["success"] = bool(obj["success"])
            for key in ("failures", "response_headers", "tls", "tags"):
                obj[key] = json.loads(obj[key])
            output.append(obj)
        return output

    def prune(self, days):
        cutoff = (datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=days)).isoformat()
        with self.connection:
            cur = self.connection.execute("DELETE FROM probes WHERE timestamp < ?", (cutoff,))
        return cur.rowcount

    def close(self):
        self.connection.close()


def summarize(results):
    grouped = defaultdict(list)
    for result in results:
        obj = result.as_dict() if isinstance(result, Result) else result
        grouped[obj["name"]].append(obj)
    output = {}
    for name, rows in sorted(grouped.items()):
        latencies = [r["latency_ms"] for r in rows]
        statuses = Counter(str(r["status"]) if r["status"] is not None else "transport_error" for r in rows)
        success = sum(bool(r["success"]) for r in rows)
        failures = Counter(message for r in rows for message in r["failures"])
        output[name] = {
            "total": len(rows),
            "successful": success,
            "failed": len(rows) - success,
            "availability_percent": round(success * 100 / len(rows), 3),
            "latency_ms": describe(latencies),
            "status_counts": dict(statuses),
            "failure_reasons": dict(failures),
            "first_observed": min(r["timestamp"] for r in rows),
            "last_observed": max(r["timestamp"] for r in rows),
        }
    return output


def anomalies(results, threshold=3.0):
    output = []
    grouped = defaultdict(list)
    for row in results:
        obj = row.as_dict() if isinstance(row, Result) else row
        grouped[obj["name"]].append(obj)
    for name, rows in grouped.items():
        latencies = [r["latency_ms"] for r in rows if r["success"]]
        if len(latencies) < 5:
            continue
        center = statistics.median(latencies)
        deviations = [abs(v - center) for v in latencies]
        mad = statistics.median(deviations)
        if mad == 0:
            continue
        for row in rows:
            score = 0.6745 * (row["latency_ms"] - center) / mad
            if row["success"] and score > threshold:
                output.append({"name": name, "timestamp": row["timestamp"], "latency_ms": row["latency_ms"], "robust_z_score": round(score, 3)})
    return output


def load_config(path):
    with open(path, encoding="utf-8") as stream:
        obj = json.load(stream)
    if not isinstance(obj, dict) or not isinstance(obj.get("endpoints"), list):
        raise SentinelError("Configuration requires an endpoints array")
    endpoints = [Endpoint.from_dict(x) for x in obj["endpoints"]]
    names = [e.name for e in endpoints]
    if len(names) != len(set(names)):
        raise SentinelError("Endpoint names must be unique")
    if not endpoints:
        raise SentinelError("No endpoints configured")
    return endpoints


def example_config():
    return {"endpoints": [
        {"name": "local-health", "url": "http://127.0.0.1:8000/health", "expected_status": [200], "timeout": 5, "retries": 1, "max_latency_ms": 1500, "tags": ["local", "health"]},
        {"name": "local-api", "url": "http://127.0.0.1:8000/api/status", "expected_status": [200, 204], "timeout": 5, "expected_headers": {"content-type": "json"}, "tags": ["local", "api"]}
    ]}


def atomic_json(path, data):
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + "." + uuid.uuid4().hex + ".tmp")
    try:
        with open(temporary, "w", encoding="utf-8") as stream:
            json.dump(data, stream, indent=2, ensure_ascii=False, allow_nan=False)
            stream.write("\n")
        os.replace(temporary, target)
    finally:
        if temporary.exists():
            temporary.unlink()


def export_csv(path, results):
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    columns = ["run_id", "name", "url", "method", "timestamp", "success", "status", "latency_ms", "bytes_read", "attempts", "error", "failures", "body_sha256"]
    with open(target, "w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        for row in results:
            obj = row.as_dict() if isinstance(row, Result) else row
            writer.writerow({key: json.dumps(obj[key]) if key == "failures" else obj.get(key) for key in columns})


def run_batch(endpoints, workers, inspect_tls, follow_redirects):
    run_id = uuid.uuid4().hex
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(workers, len(endpoints))) as pool:
        futures = {pool.submit(probe, endpoint, run_id, inspect_tls, follow_redirects): endpoint.name for endpoint in endpoints}
        for future in concurrent.futures.as_completed(futures):
            try:
                results.append(future.result())
            except Exception as exc:
                name = futures[future]
                results.append(Result(run_id, name, "", "", utcnow(), False, error=str(exc), failures=["Internal probe failure"]))
    return sorted(results, key=lambda x: x.name)


def render_results(results):
    print(f"{'ENDPOINT':28} {'STATE':8} {'STATUS':7} {'LATENCY':12} {'ATTEMPTS':8} DETAILS")
    print("-" * 100)
    for r in results:
        state = "OK" if r.success else "FAILED"
        details = "; ".join(r.failures) if r.failures else "-"
        print(f"{r.name[:28]:28} {state:8} {str(r.status or '-'):7} {r.latency_ms:9.2f} ms {r.attempts:8} {details[:90]}")


def render_summary(summary):
    print(f"{'ENDPOINT':28} {'SAMPLES':9} {'UPTIME':10} {'P50 MS':10} {'P95 MS':10} {'P99 MS':10}")
    print("-" * 85)
    for name, info in summary.items():
        latency = info["latency_ms"]
        print(f"{name[:28]:28} {info['total']:9} {info['availability_percent']:9.2f}% {latency['median']:10.2f} {latency['p95']:10.2f} {latency['p99']:10.2f}")


def parse_args(argv=None):
    parser = argparse.ArgumentParser(prog="api-sentinel", description="Self-hosted HTTP API monitoring and diagnostics")
    parser.add_argument("command", nargs="?", choices=["scan", "watch", "history", "report", "init", "prune"], default="scan")
    parser.add_argument("--config", default="api-sentinel.json")
    parser.add_argument("--url", action="append", help="URL to probe without a configuration file")
    parser.add_argument("--db", default="api-sentinel.sqlite3")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--interval", type=float, default=60)
    parser.add_argument("--cycles", type=int, default=0)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--retries", type=int, default=0)
    parser.add_argument("--method", default="GET")
    parser.add_argument("--allow-mutation", action="store_true")
    parser.add_argument("--insecure", action="store_true")
    parser.add_argument("--tls", action="store_true")
    parser.add_argument("--follow-redirects", action="store_true")
    parser.add_argument("--json-output")
    parser.add_argument("--csv-output")
    parser.add_argument("--name")
    parser.add_argument("--limit", type=int, default=1000)
    parser.add_argument("--days", type=int, default=30)
    parser.add_argument("--no-store", action="store_true")
    parser.add_argument("--version", action="version", version=VERSION)
    args = parser.parse_args(argv)
    if args.workers < 1 or args.workers > 256:
        parser.error("workers must be between 1 and 256")
    if args.interval <= 0 or args.cycles < 0 or args.limit <= 0 or args.days <= 0:
        parser.error("interval, limit and days must be positive; cycles must be nonnegative")
    return args


def load_endpoints(args):
    if args.url:
        endpoints = []
        for index, url in enumerate(args.url, 1):
            parsed = urllib.parse.urlsplit(url)
            name = f"{parsed.hostname or 'endpoint'}-{index}"
            endpoints.append(Endpoint.from_dict({"name": name, "url": url, "method": args.method, "timeout": args.timeout, "retries": args.retries, "verify_tls": not args.insecure, "allow_mutation": args.allow_mutation}))
        return endpoints
    return load_config(args.config)


def execute(args):
    if args.command == "init":
        if Path(args.config).exists():
            raise SentinelError(f"Refusing to overwrite {args.config}")
        atomic_json(args.config, example_config())
        print(f"Created {args.config}")
        return 0
    if args.command == "prune":
        db = Database(args.db)
        try:
            count = db.prune(args.days)
        finally:
            db.close()
        print(f"Removed {count} records older than {args.days} days")
        return 0
    if args.command in {"history", "report"}:
        db = Database(args.db)
        try:
            rows = db.history(name=args.name, limit=args.limit)
        finally:
            db.close()
        if args.command == "history":
            for row in reversed(rows):
                print(f"{row['timestamp']} {row['name']:28} {'OK' if row['success'] else 'FAILED':7} status={row['status']} latency={row['latency_ms']:.2f}ms")
            output = {"history": rows}
        else:
            summary = summarize(rows)
            if summary:
                render_summary(summary)
            else:
                print("No historical records")
            output = {"generated_at": utcnow(), "summary": summary, "anomalies": anomalies(rows)}
        if args.json_output:
            atomic_json(args.json_output, output)
        if args.csv_output:
            export_csv(args.csv_output, rows)
        return 0
    endpoints = load_endpoints(args)
    db = None if args.no_store else Database(args.db)
    all_results = []
    cycle = 0
    try:
        while not STOP.is_set():
            cycle += 1
            started = time.monotonic()
            results = run_batch(endpoints, args.workers, args.tls, args.follow_redirects)
            all_results.extend(results)
            print(f"\nCycle {cycle} at {utcnow()}")
            render_results(results)
            if db:
                db.save(results)
            if args.command != "watch" or (args.cycles and cycle >= args.cycles):
                break
            STOP.wait(max(0, args.interval - (time.monotonic() - started)))
    finally:
        if db:
            db.close()
    if args.json_output:
        atomic_json(args.json_output, {"generated_at": utcnow(), "results": [r.as_dict() for r in all_results], "summary": summarize(all_results), "anomalies": anomalies(all_results)})
    if args.csv_output:
        export_csv(args.csv_output, all_results)
    return 1 if any(not r.success for r in all_results) else 0


def main(argv=None):
    incoming = list(sys.argv[1:] if argv is None else argv)
    if incoming and incoming[0] == "jsonplaceholder":
        return jsonplaceholder_main(incoming[1:])
    args = parse_args(argv)
    try:
        return execute(args)
    except (SentinelError, OSError, sqlite3.Error, ValueError, json.JSONDecodeError) as exc:
        print(f"api-sentinel: {exc}", file=sys.stderr)
        return 2




@dataclass(frozen=True)
class ContractIssue:
    resource: str
    record: str
    path: str
    code: str
    message: str
    severity: str = "error"

    def as_dict(self):
        return dataclasses.asdict(self)


@dataclass(frozen=True)
class ContractField:
    name: str
    kind: str
    required: bool = True
    minimum: Optional[float] = None
    maximum: Optional[float] = None
    min_length: Optional[int] = None
    max_length: Optional[int] = None
    allow_empty: bool = False


@dataclass(frozen=True)
class ResourceContract:
    name: str
    fields: tuple
    collection_path: str
    item_path: str
    expected_count: Optional[int] = None
    foreign_keys: tuple = ()


@dataclass
class ContractReport:
    resource: str
    count: int
    passed: int
    failed: int
    issues: list
    elapsed_ms: float
    http_status: Optional[int]
    response_bytes: int
    source: str

    def as_dict(self):
        return dataclasses.asdict(self)


@dataclass
class RelationshipReport:
    name: str
    checked: int
    matched: int
    missing: int
    issues: list

    def as_dict(self):
        return dataclasses.asdict(self)


@dataclass
class AuditReport:
    timestamp: str
    base_url: str
    reports: list
    relationships: list
    performance: dict
    health: dict
    metadata: dict

    def as_dict(self):
        return dataclasses.asdict(self)


JSONPLACEHOLDER_CONTRACTS = {
    "posts": ResourceContract(
        "posts",
        (
            ContractField("userId", "integer", minimum=1),
            ContractField("id", "integer", minimum=1),
            ContractField("title", "string", min_length=1),
            ContractField("body", "string", min_length=1),
        ),
        "/posts",
        "/posts/{id}",
        100,
        (("userId", "users", "id"),),
    ),
    "comments": ResourceContract(
        "comments",
        (
            ContractField("postId", "integer", minimum=1),
            ContractField("id", "integer", minimum=1),
            ContractField("name", "string", min_length=1),
            ContractField("email", "email"),
            ContractField("body", "string", min_length=1),
        ),
        "/comments",
        "/comments/{id}",
        500,
        (("postId", "posts", "id"),),
    ),
    "albums": ResourceContract(
        "albums",
        (
            ContractField("userId", "integer", minimum=1),
            ContractField("id", "integer", minimum=1),
            ContractField("title", "string", min_length=1),
        ),
        "/albums",
        "/albums/{id}",
        100,
        (("userId", "users", "id"),),
    ),
    "photos": ResourceContract(
        "photos",
        (
            ContractField("albumId", "integer", minimum=1),
            ContractField("id", "integer", minimum=1),
            ContractField("title", "string", min_length=1),
            ContractField("url", "url"),
            ContractField("thumbnailUrl", "url"),
        ),
        "/photos",
        "/photos/{id}",
        5000,
        (("albumId", "albums", "id"),),
    ),
    "todos": ResourceContract(
        "todos",
        (
            ContractField("userId", "integer", minimum=1),
            ContractField("id", "integer", minimum=1),
            ContractField("title", "string", min_length=1),
            ContractField("completed", "boolean"),
        ),
        "/todos",
        "/todos/{id}",
        200,
        (("userId", "users", "id"),),
    ),
    "users": ResourceContract(
        "users",
        (
            ContractField("id", "integer", minimum=1),
            ContractField("name", "string", min_length=1),
            ContractField("username", "string", min_length=1),
            ContractField("email", "email"),
            ContractField("address", "object"),
            ContractField("phone", "string", min_length=1),
            ContractField("website", "string", min_length=1),
            ContractField("company", "object"),
        ),
        "/users",
        "/users/{id}",
        10,
    ),
}


class ContractValidator:
    def __init__(self, strict=False):
        self.strict = bool(strict)

    def check_type(self, value, kind):
        if kind == "integer":
            return isinstance(value, int) and not isinstance(value, bool)
        if kind == "number":
            return isinstance(value, (float, int)) and not isinstance(value, bool) and math.isfinite(value)
        if kind == "boolean":
            return isinstance(value, bool)
        if kind == "string":
            return isinstance(value, str)
        if kind == "object":
            return isinstance(value, dict)
        if kind == "array":
            return isinstance(value, list)
        if kind == "email":
            return isinstance(value, str) and bool(re.fullmatch(r"[^\s@]+@[^\s@]+\.[^\s@]+", value))
        if kind == "url":
            if not isinstance(value, str):
                return False
            parts = urllib.parse.urlsplit(value)
            return parts.scheme in {"http", "https"} and bool(parts.hostname)
        return False

    def check_field(self, resource, record, field_spec, value):
        issues = []
        path = field_spec.name
        if not self.check_type(value, field_spec.kind):
            issues.append(ContractIssue(resource, record, path, "type", f"Expected {field_spec.kind}"))
            return issues
        if isinstance(value, (float, int)) and not isinstance(value, bool):
            if field_spec.minimum is not None and value < field_spec.minimum:
                issues.append(ContractIssue(resource, record, path, "minimum", f"Value below {field_spec.minimum}"))
            if field_spec.maximum is not None and value > field_spec.maximum:
                issues.append(ContractIssue(resource, record, path, "maximum", f"Value above {field_spec.maximum}"))
        if isinstance(value, str):
            if not field_spec.allow_empty and not value.strip():
                issues.append(ContractIssue(resource, record, path, "empty", "Empty string"))
            if field_spec.min_length is not None and len(value) < field_spec.min_length:
                issues.append(ContractIssue(resource, record, path, "min_length", "String too short"))
            if field_spec.max_length is not None and len(value) > field_spec.max_length:
                issues.append(ContractIssue(resource, record, path, "max_length", "String too long"))
        return issues

    def validate_record(self, resource, contract, record, index):
        label = str(record.get("id", index)) if isinstance(record, dict) else str(index)
        if not isinstance(record, dict):
            return [ContractIssue(resource, label, "$", "type", "Expected JSON object")]
        issues = []
        field_names = {spec.name for spec in contract.fields}
        for spec in contract.fields:
            if spec.name not in record:
                if spec.required:
                    issues.append(ContractIssue(resource, label, spec.name, "missing", "Required field missing"))
                continue
            issues.extend(self.check_field(resource, label, spec, record[spec.name]))
        if self.strict:
            for unknown in sorted(set(record) - field_names):
                issues.append(ContractIssue(resource, label, unknown, "unknown", "Unexpected field", "warning"))
        if resource == "users":
            issues.extend(self.validate_user_nested(record, label))
        return issues

    def validate_user_nested(self, record, label):
        issues = []
        address = record.get("address")
        if isinstance(address, dict):
            for name in ("street", "suite", "city", "zipcode"):
                if not isinstance(address.get(name), str) or not address[name].strip():
                    issues.append(ContractIssue("users", label, "address." + name, "invalid", "Missing address component"))
            geo = address.get("geo")
            if isinstance(geo, dict):
                for axis in ("lat", "lng"):
                    try:
                        value = float(geo[axis])
                        if not math.isfinite(value):
                            raise ValueError("Nonfinite coordinate")
                        if axis == "lat" and abs(value) > 90:
                            raise ValueError("Latitude outside range")
                        if axis == "lng" and abs(value) > 180:
                            raise ValueError("Longitude outside range")
                    except (ValueError, TypeError, KeyError):
                        issues.append(ContractIssue("users", label, "address.geo." + axis, "invalid", "Invalid coordinate"))
            else:
                issues.append(ContractIssue("users", label, "address.geo", "missing", "Expected geo object"))
        company = record.get("company")
        if isinstance(company, dict):
            for name in ("name", "catchPhrase", "bs"):
                if not isinstance(company.get(name), str) or not company[name].strip():
                    issues.append(ContractIssue("users", label, "company." + name, "invalid", "Missing company field"))
        return issues

    def validate_collection(self, resource, payload, elapsed_ms=0, http_status=None, response_bytes=0, source=""):
        contract = JSONPLACEHOLDER_CONTRACTS[resource]
        if not isinstance(payload, list):
            issue = ContractIssue(resource, "$", "$", "type", "Expected collection array")
            return ContractReport(resource, 0, 0, 1, [issue.as_dict()], elapsed_ms, http_status, response_bytes, source)
        issues = []
        passed = 0
        seen = set()
        for index, record in enumerate(payload):
            record_issues = self.validate_record(resource, contract, record, index)
            if isinstance(record, dict):
                identity = record.get("id")
                if identity in seen:
                    record_issues.append(ContractIssue(resource, str(identity), "id", "duplicate", "Duplicate record ID"))
                if identity is not None:
                    seen.add(identity)
            if not any(item.severity == "error" for item in record_issues):
                passed += 1
            issues.extend(item.as_dict() for item in record_issues)
        if contract.expected_count is not None and len(payload) != contract.expected_count:
            issues.append(ContractIssue(resource, "$", "$", "count", f"Expected {contract.expected_count} records, received {len(payload)}", "warning").as_dict())
        return ContractReport(resource, len(payload), passed, len(payload) - passed, issues, elapsed_ms, http_status, response_bytes, source)


class JsonPlaceholderClient:
    def __init__(self, base_url="https://jsonplaceholder.typicode.com", timeout=12, max_bytes=16000000, retries=2, user_agent="api-sentinel/2.0", allow_external=False):
        self.base_url = base_url.rstrip("/")
        self.timeout = float(timeout)
        self.max_bytes = int(max_bytes)
        self.retries = int(retries)
        self.user_agent = user_agent
        self.allow_external = bool(allow_external)
        self.history = []
        self._validate_base()

    def _validate_base(self):
        parts = urllib.parse.urlsplit(self.base_url)
        if parts.scheme not in {"http", "https"} or not parts.hostname or parts.username or parts.password:
            raise SentinelError("Invalid JSONPlaceholder base URL")
        if not self.allow_external and (parts.scheme != "https" or parts.hostname != "jsonplaceholder.typicode.com"):
            raise SentinelError("Custom base URLs require --allow-custom-base")
        if not 0 < self.timeout <= 300:
            raise SentinelError("Invalid request timeout")
        if not 1000 <= self.max_bytes <= 100000000:
            raise SentinelError("Invalid response size limit")
        if not 0 <= self.retries <= 8:
            raise SentinelError("Invalid retry count")

    def url(self, path, query=None):
        if not path.startswith("/") or path.startswith("//"):
            raise SentinelError("Path must start with one slash")
        parts = urllib.parse.urlsplit(path)
        if parts.scheme or parts.netloc:
            raise SentinelError("Absolute paths are not accepted")
        if query:
            return self.base_url + path + "?" + urllib.parse.urlencode(query, doseq=True)
        return self.base_url + path

    def request(self, path, query=None, method="GET", body=None, expected=(200,)):
        method = method.upper()
        if method not in {"GET", "HEAD"}:
            raise SentinelError("JSONPlaceholder audit only supports GET and HEAD")
        url = self.url(path, query)
        data = None
        if body is not None:
            raise SentinelError("Request bodies are disabled in read-only audit mode")
        last_error = None
        for attempt in range(self.retries + 1):
            started = time.perf_counter()
            status = None
            response_headers = {}
            try:
                req = urllib.request.Request(url, data=data, headers={"User-Agent": self.user_agent, "Accept": "application/json"}, method=method)
                with urllib.request.urlopen(req, timeout=self.timeout) as response:
                    status = response.status
                    response_headers = dict(response.headers.items())
                    raw = response.read(self.max_bytes + 1)
                    if len(raw) > self.max_bytes:
                        raise SentinelError("Response exceeds configured byte limit")
                duration = (time.perf_counter() - started) * 1000
                if status not in expected:
                    raise SentinelError(f"Unexpected HTTP status {status} for {path}")
                parsed = None if method == "HEAD" else json.loads(raw.decode("utf-8"))
                result = {"url": url, "path": path, "method": method, "status": status, "duration_ms": duration, "bytes": len(raw), "headers": redact_headers(response_headers), "data": parsed, "attempts": attempt + 1}
                self.history.append({k: v for k, v in result.items() if k != "data"})
                return result
            except (OSError, ValueError, UnicodeError, SentinelError) as exc:
                last_error = exc
                if attempt < self.retries:
                    time.sleep(min(2.0, 0.2 * (2 ** attempt)))
        raise SentinelError(f"Request failed for {path}: {last_error}")

    def collection(self, resource):
        if resource not in JSONPLACEHOLDER_CONTRACTS:
            raise SentinelError(f"Unknown resource {resource}")
        return self.request(JSONPLACEHOLDER_CONTRACTS[resource].collection_path)

    def item(self, resource, identity):
        if resource not in JSONPLACEHOLDER_CONTRACTS:
            raise SentinelError(f"Unknown resource {resource}")
        if not isinstance(identity, int) or identity <= 0:
            raise SentinelError("Item ID must be positive")
        return self.request(JSONPLACEHOLDER_CONTRACTS[resource].item_path.format(id=identity))


class RelationshipAuditor:
    def __init__(self, collections):
        self.collections = collections

    def run(self):
        reports = []
        for resource, contract in JSONPLACEHOLDER_CONTRACTS.items():
            rows = self.collections.get(resource)
            if not isinstance(rows, list):
                continue
            for field_name, parent_resource, parent_key in contract.foreign_keys:
                parents = self.collections.get(parent_resource)
                if not isinstance(parents, list):
                    continue
                valid = {row.get(parent_key) for row in parents if isinstance(row, dict)}
                checked = 0
                matched = 0
                issues = []
                for row in rows:
                    if not isinstance(row, dict):
                        continue
                    checked += 1
                    value = row.get(field_name)
                    if value in valid:
                        matched += 1
                    else:
                        issues.append(ContractIssue(resource, str(row.get("id", "?")), field_name, "foreign_key", f"No matching {parent_resource}.{parent_key}={value}").as_dict())
                reports.append(RelationshipReport(f"{resource}.{field_name}->{parent_resource}.{parent_key}", checked, matched, checked - matched, issues))
        return reports


class CollectionProfiler:
    def __init__(self, rows):
        self.rows = rows

    def field_presence(self):
        total = len(self.rows)
        counts = Counter()
        for row in self.rows:
            if isinstance(row, dict):
                counts.update(row.keys())
        return {key: {"present": count, "missing": total - count, "fraction": count / total if total else 0} for key, count in sorted(counts.items())}

    def value_types(self):
        types = defaultdict(Counter)
        for row in self.rows:
            if not isinstance(row, dict):
                continue
            for key, value in row.items():
                if value is None:
                    kind = "null"
                elif isinstance(value, bool):
                    kind = "boolean"
                elif isinstance(value, int):
                    kind = "integer"
                elif isinstance(value, float):
                    kind = "number"
                elif isinstance(value, str):
                    kind = "string"
                elif isinstance(value, dict):
                    kind = "object"
                elif isinstance(value, list):
                    kind = "array"
                else:
                    kind = "unknown"
                types[key][kind] += 1
        return {key: dict(counts) for key, counts in sorted(types.items())}

    def string_lengths(self):
        values = defaultdict(list)
        for row in self.rows:
            if isinstance(row, dict):
                for key, value in row.items():
                    if isinstance(value, str):
                        values[key].append(len(value))
        return {key: describe(lengths) for key, lengths in sorted(values.items())}

    def numeric_ranges(self):
        values = defaultdict(list)
        for row in self.rows:
            if isinstance(row, dict):
                for key, value in row.items():
                    if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value):
                        values[key].append(value)
        return {key: describe(numbers) for key, numbers in sorted(values.items())}

    def duplicates(self):
        seen = Counter()
        for row in self.rows:
            if isinstance(row, dict) and "id" in row:
                seen[str(row["id"])] += 1
        return {key: value for key, value in sorted(seen.items()) if value > 1}

    def report(self):
        return {"count": len(self.rows), "field_presence": self.field_presence(), "value_types": self.value_types(), "string_lengths": self.string_lengths(), "numeric_ranges": self.numeric_ranges(), "duplicate_ids": self.duplicates()}


class JsonPlaceholderAuditor:
    def __init__(self, client, strict=False, workers=4, sample_size=3):
        self.client = client
        self.validator = ContractValidator(strict=strict)
        self.workers = workers
        self.sample_size = sample_size
        self.collections = {}
        self.reports = []
        self.errors = []
        self.profiles = {}
        self.item_checks = []

    def fetch_one(self, resource):
        response = self.client.collection(resource)
        report = self.validator.validate_collection(resource, response["data"], response["duration_ms"], response["status"], response["bytes"], response["url"])
        return resource, response, report

    def fetch_collections(self, resources):
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.workers) as pool:
            future_map = {pool.submit(self.fetch_one, resource): resource for resource in resources}
            for future in concurrent.futures.as_completed(future_map):
                resource = future_map[future]
                try:
                    name, response, report = future.result()
                    self.collections[name] = response["data"]
                    self.reports.append(report)
                    if isinstance(response["data"], list):
                        self.profiles[name] = CollectionProfiler(response["data"]).report()
                except Exception as exc:
                    self.errors.append({"resource": resource, "error": str(exc)})
        self.reports.sort(key=lambda report: report.resource)

    def inspect_items(self, resources):
        for resource in resources:
            rows = self.collections.get(resource)
            if not isinstance(rows, list):
                continue
            valid = [row for row in rows if isinstance(row, dict) and isinstance(row.get("id"), int)]
            selected = valid[:self.sample_size]
            for record in selected:
                identity = record["id"]
                try:
                    response = self.client.item(resource, identity)
                    item = response["data"]
                    matches = item == record
                    self.item_checks.append({"resource": resource, "id": identity, "matches_collection": matches, "status": response["status"], "duration_ms": response["duration_ms"]})
                    if not matches:
                        self.errors.append({"resource": resource, "id": identity, "error": "Collection and item payload differ"})
                except Exception as exc:
                    self.errors.append({"resource": resource, "id": identity, "error": str(exc)})

    def run(self, resources, include_items=False):
        started = time.perf_counter()
        self.fetch_collections(resources)
        if include_items:
            self.inspect_items(resources)
        relationships = RelationshipAuditor(self.collections).run()
        latencies = [entry["duration_ms"] for entry in self.client.history]
        failed = sum(report.failed for report in self.reports)
        failed += sum(report.missing for report in relationships)
        failed += len(self.errors)
        health = {"ok": failed == 0, "failures": failed, "requests": len(self.client.history), "records": sum(report.count for report in self.reports), "validated": sum(report.passed for report in self.reports), "errors": self.errors}
        metadata = {"resources": list(resources), "sample_size": self.sample_size, "item_checks": self.item_checks, "profiles": self.profiles, "request_history": self.client.history}
        performance = {"elapsed_ms": (time.perf_counter() - started) * 1000, "request_latency_ms": describe(latencies)}
        return AuditReport(utcnow(), self.client.base_url, [report.as_dict() for report in self.reports], [report.as_dict() for report in relationships], performance, health, metadata)


class JsonPlaceholderSnapshot:
    def __init__(self, report):
        self.report = report

    def fingerprint(self):
        raw = json.dumps(self.report, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        return hashlib.sha256(raw).hexdigest()

    def save(self, path):
        payload = {"format": "api-sentinel-jsonplaceholder-snapshot", "version": 1, "fingerprint": self.fingerprint(), "report": self.report}
        atomic_json(path, payload)

    @staticmethod
    def load(path):
        with open(path, "r", encoding="utf-8") as stream:
            payload = json.load(stream)
        if payload.get("format") != "api-sentinel-jsonplaceholder-snapshot":
            raise SentinelError("Invalid snapshot format")
        report = payload.get("report")
        if not isinstance(report, dict):
            raise SentinelError("Snapshot report is invalid")
        expected = hashlib.sha256(json.dumps(report, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")).hexdigest()
        if expected != payload.get("fingerprint"):
            raise SentinelError("Snapshot fingerprint mismatch")
        return JsonPlaceholderSnapshot(report)

    def compare(self, other):
        left = self.report
        right = other.report
        changes = []
        for key in ("base_url",):
            if left.get(key) != right.get(key):
                changes.append({"path": key, "old": left.get(key), "new": right.get(key)})
        left_reports = {item["resource"]: item for item in left.get("reports", [])}
        right_reports = {item["resource"]: item for item in right.get("reports", [])}
        for resource in sorted(set(left_reports) | set(right_reports)):
            old = left_reports.get(resource, {})
            new = right_reports.get(resource, {})
            for key in ("count", "passed", "failed", "http_status"):
                if old.get(key) != new.get(key):
                    changes.append({"path": f"reports.{resource}.{key}", "old": old.get(key), "new": new.get(key)})
        return {"changed": bool(changes), "changes": changes, "old_fingerprint": self.fingerprint(), "new_fingerprint": other.fingerprint()}


class JsonPlaceholderRenderer:
    def __init__(self, verbose=False):
        self.verbose = verbose

    def render(self, report):
        print("JSONPlaceholder API Audit")
        print("Base URL:", report.base_url)
        print("Timestamp:", report.timestamp)
        print("Requests:", report.health["requests"])
        print("Validated records:", report.health["validated"])
        print("Failures:", report.health["failures"])
        print("Elapsed: %.2f ms" % report.performance["elapsed_ms"])
        print()
        print(f"{'RESOURCE':14} {'RECORDS':>8} {'PASSED':>8} {'FAILED':>8} {'HTTP':>6} {'LATENCY':>12}")
        for item in report.reports:
            print(f"{item['resource']:14} {item['count']:8d} {item['passed']:8d} {item['failed']:8d} {str(item['http_status']):>6} {item['elapsed_ms']:11.2f}ms")
        if report.relationships:
            print()
            print("Relationships")
            for item in report.relationships:
                print(f"  {item['name']}: {item['matched']}/{item['checked']} matched")
        if report.health["errors"]:
            print()
            print("Request errors")
            for item in report.health["errors"]:
                print("  " + json.dumps(item, sort_keys=True))
        if self.verbose:
            for item in report.reports:
                for issue in item["issues"][:50]:
                    print(f"  {item['resource']} {issue['record']} {issue['path']}: {issue['message']}")
            for item in report.metadata["item_checks"]:
                print(f"  Item {item['resource']}/{item['id']}: {'MATCH' if item['matches_collection'] else 'MISMATCH'}")


def jsonplaceholder_parser():
    parser = argparse.ArgumentParser(prog="api-sentinel jsonplaceholder", description="Read-only JSONPlaceholder API contract and relationship audit")
    parser.add_argument("--base-url", default="https://jsonplaceholder.typicode.com")
    parser.add_argument("--allow-custom-base", action="store_true")
    parser.add_argument("--resource", action="append", choices=sorted(JSONPLACEHOLDER_CONTRACTS))
    parser.add_argument("--timeout", type=float, default=12)
    parser.add_argument("--retries", type=int, default=2)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--max-bytes", type=int, default=16000000)
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--items", action="store_true")
    parser.add_argument("--sample-size", type=int, default=3)
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--json-output")
    parser.add_argument("--snapshot")
    parser.add_argument("--compare")
    parser.add_argument("--offline-sample", action="store_true")
    parser.add_argument("--invariants", action="store_true")
    parser.add_argument("--query-suite", action="store_true")
    parser.add_argument("--query-limit", type=int, default=10)
    parser.add_argument("--inventory-output")
    parser.add_argument("--archive-output")
    parser.add_argument("--archive-input")
    parser.add_argument("--csv-directory")
    return parser


def jsonplaceholder_offline_sample():
    return {
        "users": [{"id": 1, "name": "Example User", "username": "example", "email": "example@example.org", "address": {"street": "Main", "suite": "1", "city": "Example", "zipcode": "10000", "geo": {"lat": "1", "lng": "2"}}, "phone": "555-0100", "website": "example.org", "company": {"name": "Example", "catchPhrase": "Example phrase", "bs": "example"}}],
        "posts": [{"userId": 1, "id": 1, "title": "Example post", "body": "Example content"}],
        "comments": [{"postId": 1, "id": 1, "name": "Example comment", "email": "example@example.org", "body": "Example comment body"}],
        "albums": [{"userId": 1, "id": 1, "title": "Example album"}],
        "photos": [{"albumId": 1, "id": 1, "title": "Example photo", "url": "https://example.org/photo", "thumbnailUrl": "https://example.org/thumb"}],
        "todos": [{"userId": 1, "id": 1, "title": "Example task", "completed": False}],
    }


def jsonplaceholder_main(argv):
    args = jsonplaceholder_parser().parse_args(argv)
    if args.workers < 1 or args.workers > 32:
        raise SystemExit("workers must be between 1 and 32")
    if args.sample_size < 0 or args.sample_size > 50:
        raise SystemExit("sample-size must be between 0 and 50")
    resources = args.resource or list(JSONPLACEHOLDER_CONTRACTS)
    try:
        if args.offline_sample:
            data = jsonplaceholder_offline_sample()
            validator = ContractValidator(strict=args.strict)
            reports = [validator.validate_collection(resource, data[resource], source="offline-sample").as_dict() for resource in resources]
            relations = [item.as_dict() for item in RelationshipAuditor({key: data[key] for key in resources}).run()]
            failures = sum(item["failed"] for item in reports) + sum(item["missing"] for item in relations)
            report = AuditReport(utcnow(), "offline-sample", reports, relations, {"elapsed_ms": 0.0, "request_latency_ms": {"count": 0}}, {"ok": failures == 0, "failures": failures, "requests": 0, "records": len(reports), "validated": sum(item["passed"] for item in reports), "errors": []}, {"resources": resources, "sample_size": 0, "item_checks": [], "profiles": {key: CollectionProfiler(data[key]).report() for key in resources}, "request_history": []})
        else:
            client = JsonPlaceholderClient(args.base_url, args.timeout, args.max_bytes, args.retries, allow_external=args.allow_custom_base)
            auditor = JsonPlaceholderAuditor(client, args.strict, args.workers, args.sample_size)
            report = auditor.run(resources, args.items)
        JsonPlaceholderRenderer(args.verbose).render(report)
        payload = report.as_dict()
        collections = data if args.offline_sample else auditor.collections
        if args.invariants:
            invariant_report = JsonPlaceholderInvariantChecker({key: collections[key] for key in resources if key in collections}).run()
            payload["invariants"] = invariant_report
            print("Invariant errors:", invariant_report["errors"])
            if invariant_report["errors"]:
                report.health["ok"] = False
        if args.query_suite:
            if args.offline_sample:
                raise SentinelError("Query suite requires a live API")
            suite = JsonPlaceholderQuerySuite(client).standard_cases()
            query_report = suite.run(args.workers, args.query_limit)
            payload["query_suite"] = query_report
            print("Query suite:", query_report["passed"], "passed,", query_report["failed"], "failed")
            if query_report["failed"]:
                report.health["ok"] = False
        if args.inventory_output:
            EndpointInventory(args.base_url).save(args.inventory_output)
        if args.archive_output:
            JsonPlaceholderArchive(collections).save(args.archive_output)
        if args.archive_input:
            previous_archive = JsonPlaceholderArchive.load(args.archive_input)
            payload["archive_diff"] = JsonPlaceholderDiffEngine(previous_archive.collections, collections).run()
        if args.csv_directory:
            exporter = JsonPlaceholderCSVExporter(collections)
            payload["csv_exports"] = [exporter.export(resource, str(Path(args.csv_directory) / (resource + ".csv"))) for resource in resources if resource in collections]
        payload["quality_score"] = JsonPlaceholderRiskModel(payload).report_summary()
        if args.json_output:
            atomic_json(args.json_output, payload)
        if args.snapshot:
            JsonPlaceholderSnapshot(payload).save(args.snapshot)
        if args.compare:
            previous = JsonPlaceholderSnapshot.load(args.compare)
            comparison = previous.compare(JsonPlaceholderSnapshot(payload))
            print("Snapshot comparison:", json.dumps(comparison, indent=2))
        return 0 if report.health["ok"] else 1
    except (SentinelError, OSError, ValueError, json.JSONDecodeError) as exc:
        print("api-sentinel jsonplaceholder:", exc, file=sys.stderr)
        return 2




class JsonPathResolver:
    def __init__(self, missing=None):
        self.missing = missing

    def tokens(self, expression):
        if not isinstance(expression, str) or not expression:
            raise SentinelError("Path expression must be nonempty")
        tokens = []
        buffer = []
        index = 0
        while index < len(expression):
            char = expression[index]
            if char == ".":
                if buffer:
                    tokens.append("".join(buffer))
                    buffer.clear()
                index += 1
                continue
            if char == "[":
                if buffer:
                    tokens.append("".join(buffer))
                    buffer.clear()
                end = expression.find("]", index + 1)
                if end < 0:
                    raise SentinelError("Unclosed array index")
                token = expression[index + 1:end]
                if not token.isdigit():
                    raise SentinelError("Array indices must be nonnegative integers")
                tokens.append(int(token))
                index = end + 1
                continue
            buffer.append(char)
            index += 1
        if buffer:
            tokens.append("".join(buffer))
        return tokens

    def resolve(self, obj, expression):
        current = obj
        for token in self.tokens(expression):
            if isinstance(token, int) and isinstance(current, list):
                if token >= len(current):
                    return self.missing
                current = current[token]
            elif isinstance(token, str) and isinstance(current, dict):
                if token not in current:
                    return self.missing
                current = current[token]
            else:
                return self.missing
        return current

    def exists(self, obj, expression):
        marker = object()
        resolver = JsonPathResolver(marker)
        return resolver.resolve(obj, expression) is not marker

    def select(self, rows, expression):
        return [self.resolve(row, expression) for row in rows]


class JsonPlaceholderInvariantChecker:
    def __init__(self, collections):
        self.collections = collections
        self.issues = []
        self.metrics = {}

    def issue(self, resource, record, path, code, message, severity="error"):
        self.issues.append(ContractIssue(resource, str(record), path, code, message, severity).as_dict())

    def rows(self, resource):
        value = self.collections.get(resource)
        return value if isinstance(value, list) else []

    def unique_ids(self, resource):
        ids = [row.get("id") for row in self.rows(resource) if isinstance(row, dict)]
        duplicates = {str(identity): count for identity, count in Counter(map(str, ids)).items() if count > 1}
        for identity, count in duplicates.items():
            self.issue(resource, identity, "id", "duplicate", f"ID repeated {count} times")
        self.metrics[resource + ".unique_ids"] = len(set(map(str, ids)))

    def positive_ids(self, resource):
        for row in self.rows(resource):
            if not isinstance(row, dict):
                continue
            identity = row.get("id")
            if not isinstance(identity, int) or isinstance(identity, bool) or identity < 1:
                self.issue(resource, identity, "id", "invalid", "ID must be a positive integer")

    def contiguous_ids(self, resource):
        ids = sorted(row["id"] for row in self.rows(resource) if isinstance(row, dict) and isinstance(row.get("id"), int))
        if not ids:
            return
        expected = list(range(ids[0], ids[-1] + 1))
        if len(ids) != len(expected):
            self.issue(resource, "$", "id", "gaps", "IDs are not contiguous", "warning")
        self.metrics[resource + ".min_id"] = ids[0]
        self.metrics[resource + ".max_id"] = ids[-1]

    def user_email_uniqueness(self):
        emails = defaultdict(list)
        for row in self.rows("users"):
            if isinstance(row, dict) and isinstance(row.get("email"), str):
                emails[row["email"].lower()].append(row.get("id"))
        for email, ids in emails.items():
            if len(ids) > 1:
                self.issue("users", ",".join(map(str, ids)), "email", "duplicate_email", f"Repeated email {email}")
        self.metrics["users.unique_emails"] = len(emails)

    def user_username_uniqueness(self):
        names = defaultdict(list)
        for row in self.rows("users"):
            if isinstance(row, dict) and isinstance(row.get("username"), str):
                names[row["username"].casefold()].append(row.get("id"))
        for username, ids in names.items():
            if len(ids) > 1:
                self.issue("users", ",".join(map(str, ids)), "username", "duplicate_username", f"Repeated username {username}")
        self.metrics["users.unique_usernames"] = len(names)

    def todo_completion(self):
        rows = self.rows("todos")
        completed = sum(row.get("completed") is True for row in rows if isinstance(row, dict))
        pending = sum(row.get("completed") is False for row in rows if isinstance(row, dict))
        self.metrics["todos.completed"] = completed
        self.metrics["todos.pending"] = pending
        self.metrics["todos.completion_rate"] = completed / (completed + pending) if completed + pending else None

    def post_distribution(self):
        counter = Counter(row.get("userId") for row in self.rows("posts") if isinstance(row, dict))
        self.metrics["posts.per_user"] = {str(key): value for key, value in sorted(counter.items(), key=lambda item: str(item[0]))}
        self.metrics["posts.users_with_posts"] = len(counter)

    def comment_distribution(self):
        counter = Counter(row.get("postId") for row in self.rows("comments") if isinstance(row, dict))
        self.metrics["comments.per_post"] = {str(key): value for key, value in sorted(counter.items(), key=lambda item: str(item[0]))}
        self.metrics["comments.posts_with_comments"] = len(counter)

    def album_distribution(self):
        counter = Counter(row.get("userId") for row in self.rows("albums") if isinstance(row, dict))
        self.metrics["albums.per_user"] = {str(key): value for key, value in sorted(counter.items(), key=lambda item: str(item[0]))}
        self.metrics["albums.users_with_albums"] = len(counter)

    def photo_distribution(self):
        counter = Counter(row.get("albumId") for row in self.rows("photos") if isinstance(row, dict))
        self.metrics["photos.per_album"] = {str(key): value for key, value in sorted(counter.items(), key=lambda item: str(item[0]))}
        self.metrics["photos.albums_with_photos"] = len(counter)

    def user_todo_distribution(self):
        counter = Counter(row.get("userId") for row in self.rows("todos") if isinstance(row, dict))
        self.metrics["todos.per_user"] = {str(key): value for key, value in sorted(counter.items(), key=lambda item: str(item[0]))}
        self.metrics["todos.users_with_todos"] = len(counter)

    def validate_photo_urls(self):
        for row in self.rows("photos"):
            if not isinstance(row, dict):
                continue
            for key in ("url", "thumbnailUrl"):
                value = row.get(key)
                if not isinstance(value, str):
                    continue
                parts = urllib.parse.urlsplit(value)
                if parts.scheme not in {"http", "https"} or not parts.hostname:
                    self.issue("photos", row.get("id"), key, "invalid_url", "Photo URL is malformed")
                elif parts.username or parts.password:
                    self.issue("photos", row.get("id"), key, "credentials", "Photo URL contains embedded credentials")

    def validate_text(self, resource, fields):
        for row in self.rows(resource):
            if not isinstance(row, dict):
                continue
            for field_name in fields:
                value = row.get(field_name)
                if isinstance(value, str) and value != value.strip():
                    self.issue(resource, row.get("id"), field_name, "whitespace", "Leading or trailing whitespace", "warning")
                if isinstance(value, str) and "\x00" in value:
                    self.issue(resource, row.get("id"), field_name, "nul", "Embedded NUL character")

    def validate_coordinates(self):
        for row in self.rows("users"):
            if not isinstance(row, dict):
                continue
            geo = row.get("address", {}).get("geo") if isinstance(row.get("address"), dict) else None
            if not isinstance(geo, dict):
                continue
            for key, limit in (("lat", 90), ("lng", 180)):
                try:
                    number = float(geo[key])
                    if not math.isfinite(number) or abs(number) > limit:
                        raise ValueError("Out of range")
                except (KeyError, TypeError, ValueError):
                    self.issue("users", row.get("id"), "address.geo." + key, "coordinate", "Invalid geographic coordinate")

    def run(self):
        for resource in self.collections:
            if resource in JSONPLACEHOLDER_CONTRACTS:
                self.unique_ids(resource)
                self.positive_ids(resource)
                self.contiguous_ids(resource)
        if "users" in self.collections:
            self.user_email_uniqueness()
            self.user_username_uniqueness()
            self.validate_coordinates()
        if "todos" in self.collections:
            self.todo_completion()
        if "posts" in self.collections:
            self.post_distribution()
        if "comments" in self.collections:
            self.comment_distribution()
        if "albums" in self.collections:
            self.album_distribution()
        if "photos" in self.collections:
            self.photo_distribution()
            self.validate_photo_urls()
        if "todos" in self.collections:
            self.user_todo_distribution()
        for resource, fields in {
            "posts": ("title", "body"),
            "comments": ("name", "body"),
            "albums": ("title",),
            "photos": ("title",),
            "todos": ("title",),
            "users": ("name", "username", "email"),
        }.items():
            if resource in self.collections:
                self.validate_text(resource, fields)
        return {"issues": self.issues, "metrics": self.metrics, "errors": sum(issue["severity"] == "error" for issue in self.issues)}


class JsonPlaceholderQuerySuite:
    def __init__(self, client):
        self.client = client
        self.cases = []

    def add(self, name, path, query, expected_kind, expected_length=None, property_name=None, expected_value=None):
        self.cases.append({"name": name, "path": path, "query": query, "kind": expected_kind, "length": expected_length, "property": property_name, "value": expected_value})

    def standard_cases(self):
        self.add("posts-by-user-1", "/posts", {"userId": 1}, "array", 10, "userId", 1)
        self.add("posts-by-user-2", "/posts", {"userId": 2}, "array", 10, "userId", 2)
        self.add("posts-by-user-3", "/posts", {"userId": 3}, "array", 10, "userId", 3)
        self.add("posts-by-user-4", "/posts", {"userId": 4}, "array", 10, "userId", 4)
        self.add("posts-by-user-5", "/posts", {"userId": 5}, "array", 10, "userId", 5)
        self.add("posts-by-user-6", "/posts", {"userId": 6}, "array", 10, "userId", 6)
        self.add("posts-by-user-7", "/posts", {"userId": 7}, "array", 10, "userId", 7)
        self.add("posts-by-user-8", "/posts", {"userId": 8}, "array", 10, "userId", 8)
        self.add("posts-by-user-9", "/posts", {"userId": 9}, "array", 10, "userId", 9)
        self.add("posts-by-user-10", "/posts", {"userId": 10}, "array", 10, "userId", 10)
        self.add("todos-by-user-1", "/todos", {"userId": 1}, "array", 20, "userId", 1)
        self.add("todos-by-user-2", "/todos", {"userId": 2}, "array", 20, "userId", 2)
        self.add("todos-by-user-3", "/todos", {"userId": 3}, "array", 20, "userId", 3)
        self.add("todos-by-user-4", "/todos", {"userId": 4}, "array", 20, "userId", 4)
        self.add("todos-by-user-5", "/todos", {"userId": 5}, "array", 20, "userId", 5)
        self.add("todos-by-user-6", "/todos", {"userId": 6}, "array", 20, "userId", 6)
        self.add("todos-by-user-7", "/todos", {"userId": 7}, "array", 20, "userId", 7)
        self.add("todos-by-user-8", "/todos", {"userId": 8}, "array", 20, "userId", 8)
        self.add("todos-by-user-9", "/todos", {"userId": 9}, "array", 20, "userId", 9)
        self.add("todos-by-user-10", "/todos", {"userId": 10}, "array", 20, "userId", 10)
        self.add("albums-by-user-1", "/albums", {"userId": 1}, "array", 10, "userId", 1)
        self.add("albums-by-user-2", "/albums", {"userId": 2}, "array", 10, "userId", 2)
        self.add("albums-by-user-3", "/albums", {"userId": 3}, "array", 10, "userId", 3)
        self.add("albums-by-user-4", "/albums", {"userId": 4}, "array", 10, "userId", 4)
        self.add("albums-by-user-5", "/albums", {"userId": 5}, "array", 10, "userId", 5)
        self.add("albums-by-user-6", "/albums", {"userId": 6}, "array", 10, "userId", 6)
        self.add("albums-by-user-7", "/albums", {"userId": 7}, "array", 10, "userId", 7)
        self.add("albums-by-user-8", "/albums", {"userId": 8}, "array", 10, "userId", 8)
        self.add("albums-by-user-9", "/albums", {"userId": 9}, "array", 10, "userId", 9)
        self.add("albums-by-user-10", "/albums", {"userId": 10}, "array", 10, "userId", 10)
        self.add("comments-post-1", "/comments", {"postId": 1}, "array", 5, "postId", 1)
        self.add("comments-post-2", "/comments", {"postId": 2}, "array", 5, "postId", 2)
        self.add("comments-post-3", "/comments", {"postId": 3}, "array", 5, "postId", 3)
        self.add("comments-post-4", "/comments", {"postId": 4}, "array", 5, "postId", 4)
        self.add("comments-post-5", "/comments", {"postId": 5}, "array", 5, "postId", 5)
        self.add("comments-post-6", "/comments", {"postId": 6}, "array", 5, "postId", 6)
        self.add("comments-post-7", "/comments", {"postId": 7}, "array", 5, "postId", 7)
        self.add("comments-post-8", "/comments", {"postId": 8}, "array", 5, "postId", 8)
        self.add("comments-post-9", "/comments", {"postId": 9}, "array", 5, "postId", 9)
        self.add("comments-post-10", "/comments", {"postId": 10}, "array", 5, "postId", 10)
        self.add("photos-album-1", "/photos", {"albumId": 1}, "array", 50, "albumId", 1)
        self.add("photos-album-2", "/photos", {"albumId": 2}, "array", 50, "albumId", 2)
        self.add("photos-album-3", "/photos", {"albumId": 3}, "array", 50, "albumId", 3)
        self.add("photos-album-4", "/photos", {"albumId": 4}, "array", 50, "albumId", 4)
        self.add("photos-album-5", "/photos", {"albumId": 5}, "array", 50, "albumId", 5)
        self.add("photos-album-6", "/photos", {"albumId": 6}, "array", 50, "albumId", 6)
        self.add("photos-album-7", "/photos", {"albumId": 7}, "array", 50, "albumId", 7)
        self.add("photos-album-8", "/photos", {"albumId": 8}, "array", 50, "albumId", 8)
        self.add("photos-album-9", "/photos", {"albumId": 9}, "array", 50, "albumId", 9)
        self.add("photos-album-10", "/photos", {"albumId": 10}, "array", 50, "albumId", 10)
        return self

    def execute_case(self, case):
        started = time.perf_counter()
        try:
            response = self.client.request(case["path"], case["query"])
            payload = response["data"]
            errors = []
            if case["kind"] == "array" and not isinstance(payload, list):
                errors.append("Expected array response")
            if case["length"] is not None and isinstance(payload, list) and len(payload) != case["length"]:
                errors.append(f"Expected {case['length']} records, got {len(payload)}")
            if case["property"] is not None and isinstance(payload, list):
                for index, row in enumerate(payload):
                    if not isinstance(row, dict) or row.get(case["property"]) != case["value"]:
                        errors.append(f"Record {index} failed property filter")
                        if len(errors) >= 10:
                            break
            return {"name": case["name"], "ok": not errors, "errors": errors, "duration_ms": response["duration_ms"], "records": len(payload) if isinstance(payload, list) else None}
        except Exception as exc:
            return {"name": case["name"], "ok": False, "errors": [str(exc)], "duration_ms": (time.perf_counter() - started) * 1000, "records": None}

    def run(self, workers=4, limit=None):
        cases = self.cases if limit is None else self.cases[:limit]
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            results = list(pool.map(self.execute_case, cases))
        latencies = [result["duration_ms"] for result in results]
        return {"total": len(results), "passed": sum(result["ok"] for result in results), "failed": sum(not result["ok"] for result in results), "latency_ms": describe(latencies), "results": results}


class LatencyTrendAnalyzer:
    def __init__(self, samples):
        self.samples = [float(value) for value in samples if isinstance(value, (int, float)) and math.isfinite(value) and value >= 0]

    def moving_average(self, window):
        if window < 1:
            raise SentinelError("Window must be positive")
        output = []
        running = 0.0
        for index, value in enumerate(self.samples):
            running += value
            if index >= window:
                running -= self.samples[index - window]
            output.append(running / min(window, index + 1))
        return output

    def exponential_average(self, alpha=0.2):
        if not 0 < alpha <= 1:
            raise SentinelError("Alpha must be between zero and one")
        output = []
        previous = None
        for value in self.samples:
            previous = value if previous is None else alpha * value + (1 - alpha) * previous
            output.append(previous)
        return output

    def median_absolute_deviation(self):
        if not self.samples:
            return None
        median = statistics.median(self.samples)
        return statistics.median(abs(value - median) for value in self.samples)

    def outliers(self, multiplier=3.5):
        if len(self.samples) < 3:
            return []
        median = statistics.median(self.samples)
        mad = self.median_absolute_deviation()
        if mad is None or mad == 0:
            return []
        return [{"index": index, "value": value, "modified_z": 0.6745 * (value - median) / mad} for index, value in enumerate(self.samples) if abs(0.6745 * (value - median) / mad) > multiplier]

    def linear_slope(self):
        n = len(self.samples)
        if n < 2:
            return None
        mean_x = (n - 1) / 2
        mean_y = sum(self.samples) / n
        numerator = sum((index - mean_x) * (value - mean_y) for index, value in enumerate(self.samples))
        denominator = sum((index - mean_x) ** 2 for index in range(n))
        return numerator / denominator if denominator else None

    def report(self):
        return {"statistics": describe(self.samples), "moving_average_5": self.moving_average(5), "exponential_average": self.exponential_average(), "median_absolute_deviation": self.median_absolute_deviation(), "outliers": self.outliers(), "linear_slope": self.linear_slope()}


class EndpointInventory:
    def __init__(self, base_url="https://jsonplaceholder.typicode.com"):
        self.base_url = base_url.rstrip("/")

    def routes(self):
        output = []
        for resource, contract in JSONPLACEHOLDER_CONTRACTS.items():
            output.append({"name": resource + "-collection", "method": "GET", "url": self.base_url + contract.collection_path, "expected_status": [200], "tags": ["jsonplaceholder", "collection", resource]})
            output.append({"name": resource + "-first-item", "method": "GET", "url": self.base_url + contract.item_path.format(id=1), "expected_status": [200], "tags": ["jsonplaceholder", "item", resource]})
        return output

    def config(self):
        return {"endpoints": self.routes()}

    def save(self, path):
        atomic_json(path, self.config())


class JsonPlaceholderCSVExporter:
    def __init__(self, collections):
        self.collections = collections

    def flattened(self, obj, prefix=""):
        result = {}
        if isinstance(obj, dict):
            for key, value in obj.items():
                path = prefix + "." + str(key) if prefix else str(key)
                result.update(self.flattened(value, path))
        elif isinstance(obj, list):
            result[prefix] = json.dumps(obj, ensure_ascii=False)
        else:
            result[prefix] = obj
        return result

    def rows(self, resource):
        payload = self.collections.get(resource, [])
        if not isinstance(payload, list):
            return []
        return [self.flattened(row) for row in payload if isinstance(row, dict)]

    def export(self, resource, path):
        rows = self.rows(resource)
        fields = sorted({key for row in rows for key in row})
        destination = Path(path)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("w", encoding="utf-8", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=fields)
            writer.writeheader()
            writer.writerows(rows)
        return {"resource": resource, "path": str(destination), "records": len(rows), "fields": fields}


class JsonPlaceholderDiffEngine:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def by_id(self, records):
        return {str(row["id"]): row for row in records if isinstance(row, dict) and "id" in row}

    def compare_resource(self, resource):
        left = self.by_id(self.left.get(resource, []))
        right = self.by_id(self.right.get(resource, []))
        added = sorted(set(right) - set(left))
        removed = sorted(set(left) - set(right))
        changed = []
        for identity in sorted(set(left) & set(right)):
            if left[identity] != right[identity]:
                changed.append({"id": identity, "fields": self.compare_record(left[identity], right[identity])})
        return {"resource": resource, "added": added, "removed": removed, "changed": changed, "unchanged": len(set(left) & set(right)) - len(changed)}

    def compare_record(self, left, right):
        fields = []
        for key in sorted(set(left) | set(right)):
            if left.get(key) != right.get(key):
                fields.append({"field": key, "before": left.get(key), "after": right.get(key)})
        return fields

    def run(self):
        return [self.compare_resource(resource) for resource in sorted(set(self.left) | set(self.right))]


class JsonPlaceholderArchive:
    def __init__(self, collections):
        self.collections = collections

    def checksums(self):
        output = {}
        for resource, rows in sorted(self.collections.items()):
            raw = json.dumps(rows, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
            output[resource] = hashlib.sha256(raw).hexdigest()
        return output

    def payload(self):
        return {"format": "api-sentinel-jsonplaceholder-archive", "version": 1, "created_at": utcnow(), "checksums": self.checksums(), "collections": self.collections}

    def save(self, path):
        atomic_json(path, self.payload())

    @staticmethod
    def load(path):
        with open(path, "r", encoding="utf-8") as stream:
            payload = json.load(stream)
        if payload.get("format") != "api-sentinel-jsonplaceholder-archive":
            raise SentinelError("Unsupported archive format")
        collections = payload.get("collections")
        if not isinstance(collections, dict):
            raise SentinelError("Archive collections are invalid")
        archive = JsonPlaceholderArchive(collections)
        if archive.checksums() != payload.get("checksums"):
            raise SentinelError("Archive checksum mismatch")
        return archive


class JsonPlaceholderRiskModel:
    def __init__(self, audit_report):
        self.report = audit_report

    def score(self):
        reports = self.report.get("reports", [])
        relationships = self.report.get("relationships", [])
        total = sum(item.get("count", 0) for item in reports)
        failed = sum(item.get("failed", 0) for item in reports)
        missing = sum(item.get("missing", 0) for item in relationships)
        requests = self.report.get("health", {}).get("requests", 0)
        request_errors = len(self.report.get("health", {}).get("errors", []))
        score = 0.0
        if total:
            score += 60 * failed / total
        if relationships:
            checked = sum(item.get("checked", 0) for item in relationships)
            if checked:
                score += 25 * missing / checked
        if requests:
            score += 15 * min(1, request_errors / requests)
        return min(100, max(0, score))

    def category(self):
        value = self.score()
        if value >= 70:
            return "critical"
        if value >= 40:
            return "high"
        if value >= 15:
            return "moderate"
        if value > 0:
            return "low"
        return "none"

    def report_summary(self):
        return {"score": round(self.score(), 3), "category": self.category(), "interpretation": "Data quality and API contract deviation score, not a vulnerability assessment"}




class AvailabilityWindow:
    def __init__(self, samples):
        self.samples = list(samples)

    def uptime_fraction(self):
        if not self.samples:
            return None
        return sum(bool(sample.get("success")) for sample in self.samples) / len(self.samples)

    def failure_streaks(self):
        streaks = []
        current = 0
        for sample in self.samples:
            if sample.get("success"):
                if current:
                    streaks.append(current)
                current = 0
            else:
                current += 1
        if current:
            streaks.append(current)
        return streaks

    def success_streaks(self):
        streaks = []
        current = 0
        for sample in self.samples:
            if sample.get("success"):
                current += 1
            else:
                if current:
                    streaks.append(current)
                current = 0
        if current:
            streaks.append(current)
        return streaks

    def status_distribution(self):
        counter = Counter(str(sample.get("status", "none")) for sample in self.samples)
        return dict(sorted(counter.items()))

    def error_distribution(self):
        counter = Counter(str(sample.get("error")) for sample in self.samples if sample.get("error"))
        return dict(sorted(counter.items()))

    def latency_distribution(self):
        values = [sample.get("latency_ms") for sample in self.samples]
        values = [float(value) for value in values if isinstance(value, (float, int)) and math.isfinite(value)]
        return LatencyTrendAnalyzer(values).report()

    def report(self):
        return {
            "samples": len(self.samples),
            "uptime_fraction": self.uptime_fraction(),
            "failure_streaks": self.failure_streaks(),
            "success_streaks": self.success_streaks(),
            "status_distribution": self.status_distribution(),
            "error_distribution": self.error_distribution(),
            "latency_distribution": self.latency_distribution(),
        }


class ApiBaselineEvaluator:
    def __init__(self, baseline, observed):
        self.baseline = baseline
        self.observed = observed

    def latency_change(self):
        before = self.baseline.get("latency_ms")
        after = self.observed.get("latency_ms")
        if before is None or after is None:
            return None
        if before == 0:
            return None
        return (after - before) / before * 100

    def availability_change(self):
        before = self.baseline.get("uptime_fraction")
        after = self.observed.get("uptime_fraction")
        if before is None or after is None:
            return None
        return after - before

    def error_rate_change(self):
        before = self.baseline.get("error_rate")
        after = self.observed.get("error_rate")
        if before is None or after is None:
            return None
        return after - before

    def assess(self, max_latency_regression_pct=30, min_availability_change=-0.02):
        latency = self.latency_change()
        availability = self.availability_change()
        errors = self.error_rate_change()
        warnings = []
        if latency is not None and latency > max_latency_regression_pct:
            warnings.append("Latency regression exceeds threshold")
        if availability is not None and availability < min_availability_change:
            warnings.append("Availability declined beyond threshold")
        if errors is not None and errors > 0:
            warnings.append("Error rate increased")
        return {
            "passed": not warnings,
            "latency_change_pct": latency,
            "availability_change": availability,
            "error_rate_change": errors,
            "warnings": warnings,
        }


class RequestBudget:
    def __init__(self, max_requests=100, max_seconds=300, max_bytes=100000000):
        self.max_requests = max_requests
        self.max_seconds = max_seconds
        self.max_bytes = max_bytes
        self.requests = 0
        self.bytes = 0
        self.started = time.monotonic()
        self.lock = threading.Lock()

    def reserve(self):
        with self.lock:
            if self.requests >= self.max_requests:
                raise SentinelError("Request budget exhausted")
            if time.monotonic() - self.started >= self.max_seconds:
                raise SentinelError("Time budget exhausted")
            self.requests += 1
            return self.requests

    def account_bytes(self, count):
        with self.lock:
            self.bytes += count
            if self.bytes > self.max_bytes:
                raise SentinelError("Byte budget exhausted")

    def remaining(self):
        with self.lock:
            return {
                "requests": max(0, self.max_requests - self.requests),
                "seconds": max(0, self.max_seconds - (time.monotonic() - self.started)),
                "bytes": max(0, self.max_bytes - self.bytes),
            }


class JsonPlaceholderSummaryBuilder:
    def __init__(self, collections):
        self.collections = collections

    def counts(self):
        return {resource: len(rows) if isinstance(rows, list) else None for resource, rows in sorted(self.collections.items())}

    def user_activity(self):
        users = self.collections.get("users", [])
        posts = self.collections.get("posts", [])
        todos = self.collections.get("todos", [])
        albums = self.collections.get("albums", [])
        post_counts = Counter(row.get("userId") for row in posts if isinstance(row, dict))
        todo_counts = Counter(row.get("userId") for row in todos if isinstance(row, dict))
        album_counts = Counter(row.get("userId") for row in albums if isinstance(row, dict))
        result = []
        for user in users:
            if not isinstance(user, dict):
                continue
            identity = user.get("id")
            result.append({
                "user_id": identity,
                "posts": post_counts[identity],
                "todos": todo_counts[identity],
                "albums": album_counts[identity],
            })
        return result

    def post_engagement(self):
        posts = self.collections.get("posts", [])
        comments = self.collections.get("comments", [])
        counts = Counter(row.get("postId") for row in comments if isinstance(row, dict))
        return [{"post_id": row.get("id"), "comments": counts[row.get("id")]} for row in posts if isinstance(row, dict)]

    def album_inventory(self):
        albums = self.collections.get("albums", [])
        photos = self.collections.get("photos", [])
        counts = Counter(row.get("albumId") for row in photos if isinstance(row, dict))
        return [{"album_id": row.get("id"), "photos": counts[row.get("id")]} for row in albums if isinstance(row, dict)]

    def summary(self):
        return {
            "counts": self.counts(),
            "user_activity": self.user_activity(),
            "post_engagement": self.post_engagement(),
            "album_inventory": self.album_inventory(),
        }


if __name__ == "__main__":
    signal.signal(signal.SIGINT, lambda *_: STOP.set())
    signal.signal(signal.SIGTERM, lambda *_: STOP.set())
    sys.exit(main())
