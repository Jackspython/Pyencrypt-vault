#!/usr/bin/env python3
"""
enc10.py — Multi-Version Python Native Compiler & Bundle Packager
Supports single-version Cython compilation or multi-target pre-built vault packaging
(Python 3.11, 3.12, 3.13, 3.14 across arm64, arm32, win).
"""

from __future__ import annotations

import argparse
import ast
import base64
import datetime
import hashlib
import hmac
import io
import os
import platform
import random
import re
import secrets
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

# Import protection injection module
try:
    from inject_protection import inject_into_text, _parse_datetime
except ImportError:
    # Inline fallback if inject_protection.py is not in PYTHONPATH
    def _parse_datetime(date_str: str) -> datetime.datetime:
        cleaned = date_str.strip()
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d"):
            try:
                return datetime.datetime.strptime(cleaned, fmt)
            except ValueError:
                continue
        raise ValueError(f"Invalid date format: {date_str}")

    def inject_into_text(source: str, expiry=None, expiry_msg=None, password=None) -> str:
        return source

TEMP_NAME = ".杰克"
PY_VERSIONS = ["3.10", "3.11", "3.12", "3.13", "3.14"]
CHUNK = 24
QUIET = False
RNG = random.SystemRandom()
MAX_BUNDLE_KEY = 128
MAX_ADD_BINARY = 512 * 1024 * 1024
MAX_SOURCE = 8 * 1024 * 1024
MAX_LAUNCHER_BYTES = 128 * 1024 * 1024

_HAS_MATCH = hasattr(ast, "Match")
_MATCH_CASE = getattr(ast, "match_case", None)
_TRY_STAR = getattr(ast, "TryStar", None)
_MATCH_AS = getattr(ast, "MatchAs", None)
_MATCH_STAR = getattr(ast, "MatchStar", None)
_MATCH_MAPPING = getattr(ast, "MatchMapping", None)

_FLAG_CACHE: dict[tuple[str, str], bool] = {}
_COMBINED_CACHE: dict[tuple[str, tuple[str, ...], str], bool] = {}


def log(msg: str):
    if not QUIET:
        print(msg)


def warn(msg: str):
    print(f"[!] {msg}", file=sys.stderr)


def derive_pyver() -> str:
    return f"{sys.version_info.major}.{sys.version_info.minor}"


def _fresh(n: int = 8) -> str:
    return "_0x" + "".join(RNG.choice("0123456789abcdef") for _ in range(n))


def _rname(prefix: str = "_f", n: int = 10) -> str:
    return prefix + "".join(RNG.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(n))


def _pyid(n: int = 12) -> str:
    return "_0x" + "".join(RNG.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(n))


def _cc_argv(cc: str) -> list[str]:
    return shlex.split(cc)


def _cc_exists(cc: str) -> bool:
    parts = _cc_argv(cc)
    if not parts:
        return False
    first = parts[0]
    if "/" in first or "\\" in first:
        p = Path(first)
        try:
            return p.is_file() and os.access(p, os.X_OK)
        except OSError:
            return False
    return shutil.which(first) is not None


def _is_android() -> bool:
    if "ANDROID_ROOT" in os.environ or "ANDROID_DATA" in os.environ:
        return True
    try:
        return "android" in platform.platform().lower()
    except Exception:
        return False


def _validate_gcc(spec: str) -> str:
    parts = _cc_argv(spec)
    if not parts:
        raise ValueError("empty compiler spec")
    if any(ch in spec for ch in "\n\r\t;|&$`<>\"'\\"):
        raise ValueError(f"unsafe characters in compiler spec: {spec!r}")
    first = parts[0]
    if any(c.isspace() for c in first) or first.startswith("-"):
        raise ValueError(f"invalid compiler binary: {first!r}")
    if not _cc_exists(spec):
        raise ValueError(f"compiler not found: {first}")
    if len(parts) > 1:
        for extra in parts[1:]:
            if extra.startswith("-"):
                raise ValueError(
                    f"compiler wrapper arguments are not allowed: {extra!r}"
                )
    resolved = shutil.which(first) if "/" not in first else first
    if resolved:
        base = os.path.basename(resolved).lower()
        if "gcc" not in base and not base.startswith("cc") and "clang" not in base:
            raise ValueError(f"compiler is not GCC/clang-like: {resolved}")
    return spec


def gcc_supports_flag(cc: str, flag: str) -> bool:
    key = (cc, flag)
    if key in _FLAG_CACHE:
        return _FLAG_CACHE[key]
    try:
        with tempfile.NamedTemporaryFile(suffix=".c", delete=False, mode="w") as f:
            f.write("int main(void){return 0;}\n")
            tmp_src = f.name
        tmp_out = tmp_src + ".out"
        try:
            r = subprocess.run(
                _cc_argv(cc) + [flag, "-x", "c", tmp_src, "-o", tmp_out],
                capture_output=True, text=True, timeout=30,
            )
            stderr = (r.stderr or "").lower()
            bad = (
                "not supported" in stderr
                or "unknown argument" in stderr
                or "unrecognized" in stderr
                or "is not supported" in stderr
                or "unknown option" in stderr
                or "invalid option" in stderr
                or "ignoring option" in stderr
            )
            ok = (r.returncode == 0) and not bad
        finally:
            for p in (tmp_src, tmp_out):
                try:
                    os.unlink(p)
                except OSError:
                    pass
        _FLAG_CACHE[key] = ok
        return ok
    except Exception:
        _FLAG_CACHE[key] = False
        return False


def gcc_accepts_combo(cc: str, base_flags: tuple[str, ...], flag: str) -> bool:
    key = (cc, base_flags, flag)
    if key in _COMBINED_CACHE:
        return _COMBINED_CACHE[key]
    try:
        with tempfile.NamedTemporaryFile(suffix=".c", delete=False, mode="w") as f:
            f.write("int main(void){return 0;}\n")
            tmp_src = f.name
        tmp_out = tmp_src + ".out"
        try:
            r = subprocess.run(
                _cc_argv(cc) + list(base_flags) + [flag, "-x", "c", tmp_src, "-o", tmp_out],
                capture_output=True, text=True, timeout=30,
            )
            stderr = (r.stderr or "").lower()
            bad = (
                "not supported" in stderr
                or "unknown argument" in stderr
                or "unrecognized" in stderr
                or "is not supported" in stderr
                or "unknown option" in stderr
                or "invalid option" in stderr
                or "ignoring option" in stderr
            )
            ok = (r.returncode == 0) and not bad
        finally:
            for p in (tmp_src, tmp_out):
                try:
                    os.unlink(p)
                except OSError:
                    pass
        _COMBINED_CACHE[key] = ok
        return ok
    except Exception:
        _COMBINED_CACHE[key] = False
        return False


def filter_supported_flags(cc: str, flags: list[str], base: tuple[str, ...] = ()) -> list[str]:
    kept = []
    dropped = []
    seen = set()
    for f in flags:
        if f in seen:
            continue
        seen.add(f)
        if any(ch in f for ch in "\n\r\t ;|&$`<>\"'\\"):
            dropped.append(f)
            continue
        if f in ("-O0", "-O1", "-O2", "-O3", "-s", "-fPIC", "-fPIE", "-pie",
                 "-fvisibility=hidden", "-ffunction-sections", "-fdata-sections"):
            kept.append(f)
            continue
        if base:
            ok = gcc_accepts_combo(cc, base, f)
        else:
            ok = gcc_supports_flag(cc, f)
        if ok:
            kept.append(f)
        else:
            dropped.append(f)
    if dropped and not QUIET:
        print(f"[*] GCC rejected {len(dropped)} flag(s): {', '.join(dropped)}")
    return kept


class NameMangler(ast.NodeTransformer):
    def __init__(self):
        self.renames: dict[str, str] = {}
        self.scopes: list[set[str]] = [set()]
        self.imported: set[str] = set()
        self.builtins = set(dir(__builtins__)) | {
            "self", "cls", "super", "True", "False", "None",
            "__name__", "__file__", "__doc__", "__package__", "__spec__",
            "__builtins__", "__loader__", "__cached__",
        }

    def _declare(self, name: str):
        if name:
            self.scopes[-1].add(name)

    def _visible(self, name: str) -> bool:
        for s in reversed(self.scopes):
            if name in s:
                return True
        return False

    def _push(self):
        self.scopes.append(set())

    def _pop(self):
        if len(self.scopes) > 1:
            self.scopes.pop()

    def _collect_imports(self, tree: ast.AST):
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for a in node.names:
                    self.imported.add((a.asname or a.name).split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                for a in node.names:
                    self.imported.add(a.asname or a.name)

    def _predeclare_scope(self, body: list):
        for node in body:
            self._predeclare_stmt(node)

    def _predeclare_stmt(self, node):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            self._declare(node.name)
            return
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for a in node.names:
                self._declare((a.asname or a.name).split(".")[0])
            return
        if isinstance(node, ast.Assign):
            for t in node.targets:
                self._declare_target(t)
            return
        if isinstance(node, ast.AnnAssign):
            self._declare_target(node.target)
            return
        if isinstance(node, ast.AugAssign):
            self._declare_target(node.target)
            return
        if isinstance(node, (ast.For, ast.AsyncFor)):
            self._declare_target(node.target)
            self._predeclare_scope(node.body)
            self._predeclare_scope(node.orelse)
            return
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for it in node.items:
                if it.optional_vars is not None:
                    self._declare_target(it.optional_vars)
            self._predeclare_scope(node.body)
            return
        if isinstance(node, (ast.If, ast.While)):
            self._predeclare_scope(node.body)
            self._predeclare_scope(node.orelse)
            return
        if isinstance(node, ast.Try):
            self._predeclare_scope(node.body)
            for h in node.handlers:
                if h.name:
                    self._declare(h.name)
                self._predeclare_scope(h.body)
            self._predeclare_scope(node.orelse)
            self._predeclare_scope(node.finalbody)
            return
        if _TRY_STAR is not None and isinstance(node, _TRY_STAR):
            self._predeclare_scope(node.body)
            for h in node.handlers:
                if h.name:
                    self._declare(h.name)
                self._predeclare_scope(h.body)
            self._predeclare_scope(node.orelse)
            self._predeclare_scope(node.finalbody)
            return
        if _HAS_MATCH and isinstance(node, ast.Match):
            self._predeclare_scope(node.cases)
            return
        if _MATCH_CASE is not None and isinstance(node, _MATCH_CASE):
            for sub in ast.walk(node.pattern):
                if _MATCH_AS is not None and isinstance(sub, _MATCH_AS) and sub.name:
                    self._declare(sub.name)
                elif _MATCH_STAR is not None and isinstance(sub, _MATCH_STAR) and sub.name:
                    self._declare(sub.name)
                elif _MATCH_MAPPING is not None and isinstance(sub, _MATCH_MAPPING) and sub.rest:
                    self._declare(sub.rest)
            self._predeclare_scope(node.body)
            return

    def _declare_target(self, target):
        if isinstance(target, ast.Name):
            self._declare(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for el in target.elts:
                self._declare_target(el)
        elif isinstance(target, ast.Starred):
            self._declare_target(target.value)

    def _rename(self, name: str) -> str:
        if not name:
            return name
        if name in self.builtins or name in self.imported:
            return name
        if name.startswith("__") and name.endswith("__"):
            return name
        if not self._visible(name):
            return name
        if name not in self.renames:
            self.renames[name] = _fresh()
        return self.renames[name]

    def visit_Module(self, node: ast.Module):
        self._predeclare_scope(node.body)
        for stmt in node.body:
            self.visit(stmt)
        return node

    def _visit_func(self, node):
        self._declare(node.name)
        if not node.decorator_list:
            node.name = self._rename(node.name)
        self._push()
        a = node.args
        for arg in list(getattr(a, "posonlyargs", [])) + list(a.args) + list(a.kwonlyargs):
            self._declare(arg.arg)
        if a.vararg:
            self._declare(a.vararg.arg)
        if a.kwarg:
            self._declare(a.kwarg.arg)
        for arg in list(getattr(a, "posonlyargs", [])) + list(a.args) + list(a.kwonlyargs):
            arg.arg = self._rename(arg.arg)
        if a.vararg:
            a.vararg.arg = self._rename(a.vararg.arg)
        if a.kwarg:
            a.kwarg.arg = self._rename(a.kwarg.arg)
        for d in node.decorator_list:
            self.visit(d)
        if node.returns is not None:
            self.visit(node.returns)
        for d in getattr(a, "defaults", []):
            self.visit(d)
        for d in getattr(a, "kw_defaults", []):
            if d is not None:
                self.visit(d)
        self._predeclare_scope(node.body)
        for stmt in node.body:
            self.visit(stmt)
        self._pop()
        return node

    def visit_FunctionDef(self, node):
        return self._visit_func(node)

    def visit_AsyncFunctionDef(self, node):
        return self._visit_func(node)

    def visit_Lambda(self, node: ast.Lambda):
        self._push()
        a = node.args
        for arg in list(getattr(a, "posonlyargs", [])) + list(a.args) + list(a.kwonlyargs):
            self._declare(arg.arg)
        if a.vararg:
            self._declare(a.vararg.arg)
        if a.kwarg:
            self._declare(a.kwarg.arg)
        for arg in list(getattr(a, "posonlyargs", [])) + list(a.args) + list(a.kwonlyargs):
            arg.arg = self._rename(arg.arg)
        if a.vararg:
            a.vararg.arg = self._rename(a.vararg.arg)
        if a.kwarg:
            a.kwarg.arg = self._rename(a.kwarg.arg)
        for d in getattr(a, "defaults", []):
            self.visit(d)
        for d in getattr(a, "kw_defaults", []):
            if d is not None:
                self.visit(d)
        self.visit(node.body)
        self._pop()
        return node

    def visit_ClassDef(self, node: ast.ClassDef):
        self._declare(node.name)
        node.name = self._rename(node.name)
        for b in node.bases:
            self.visit(b)
        for k in node.keywords:
            self.visit(k)
        for d in node.decorator_list:
            self.visit(d)
        self._push()
        self._predeclare_scope(node.body)
        for stmt in node.body:
            self.visit(stmt)
        self._pop()
        return node

    def visit_Name(self, node: ast.Name):
        if isinstance(node.ctx, ast.Load):
            node.id = self._rename(node.id)
        elif isinstance(node.ctx, ast.Store):
            self._declare(node.id)
            node.id = self._rename(node.id)
        elif isinstance(node.ctx, ast.Del):
            node.id = self._rename(node.id)
        return node

    def visit_Attribute(self, node: ast.Attribute):
        self.visit(node.value)
        return node

    def visit_keyword(self, node: ast.keyword):
        if node.value is not None:
            self.visit(node.value)
        return node

    def visit_arg(self, node: ast.arg):
        node.arg = self._rename(node.arg)
        if node.annotation is not None:
            self.visit(node.annotation)
        return node

    def visit_Global(self, node: ast.Global):
        node.names = [self._rename(n) for n in node.names]
        return node

    def visit_Nonlocal(self, node: ast.Nonlocal):
        node.names = [self._rename(n) for n in node.names]
        return node

    def visit_ExceptHandler(self, node: ast.ExceptHandler):
        if node.type is not None:
            self.visit(node.type)
        if node.name:
            self._declare(node.name)
            node.name = self._rename(node.name)
        for stmt in node.body:
            self.visit(stmt)
        return node

    def _visit_comprehension(self, generators, elt_visitor):
        self._push()
        for gen in generators:
            self._declare_target(gen.target)
            if gen.iter is not None:
                self.visit(gen.iter)
            for if_ in gen.ifs:
                self.visit(if_)
            target = gen.target
            self._rename_target(target)
        elt_visitor()
        self._pop()

    def _rename_target(self, target):
        if isinstance(target, ast.Name):
            target.id = self._rename(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            for el in target.elts:
                self._rename_target(el)
        elif isinstance(target, ast.Starred):
            self._rename_target(target.value)

    def visit_ListComp(self, node: ast.ListComp):
        self._visit_comprehension(node.generators, lambda: self.visit(node.elt))
        return node

    def visit_SetComp(self, node: ast.SetComp):
        self._visit_comprehension(node.generators, lambda: self.visit(node.elt))
        return node

    def visit_GeneratorExp(self, node: ast.GeneratorExp):
        self._visit_comprehension(node.generators, lambda: self.visit(node.elt))
        return node

    def visit_DictComp(self, node: ast.DictComp):
        def _both():
            self.visit(node.key)
            self.visit(node.value)
        self._visit_comprehension(node.generators, _both)
        return node

    def run(self, tree: ast.AST) -> ast.AST:
        self._collect_imports(tree)
        if isinstance(tree, ast.Module):
            return self.visit_Module(tree)
        return self.visit(tree)


class StringHider(ast.NodeTransformer):
    def __init__(self, key: bytes):
        self.key = key
        self._fstring_depth = 0

    def visit_JoinedStr(self, node: ast.JoinedStr):
        self._fstring_depth += 1
        self.generic_visit(node)
        self._fstring_depth -= 1
        return node

    def visit_FormattedValue(self, node: ast.FormattedValue):
        self._fstring_depth += 1
        self.generic_visit(node)
        self._fstring_depth -= 1
        return node

    def visit_Constant(self, node: ast.Constant):
        if self._fstring_depth:
            return node
        if not isinstance(node.value, str) or not node.value:
            return node
        data = node.value.encode("utf-8")
        enc = bytes(b ^ self.key[i % len(self.key)] for i, b in enumerate(data))
        payload = ",".join(str(x) for x in enc)
        call = ast.Call(
            func=ast.Name(id="_0xdeobf", ctx=ast.Load()),
            args=[ast.Constant(value=payload)],
            keywords=[],
        )
        return ast.copy_location(call, node)


class OpaqueInjector(ast.NodeTransformer):
    def visit_FunctionDef(self, node: ast.FunctionDef):
        self.generic_visit(node)
        if node.body:
            opaque = ast.If(
                test=ast.Call(
                    func=ast.Name(id="_0xopaque", ctx=ast.Load()),
                    args=[],
                    keywords=[],
                ),
                body=[ast.Pass()],
                orelse=[],
            )
            node.body.insert(0, opaque)
        return node

    visit_AsyncFunctionDef = visit_FunctionDef


class ASTObfuscator:
    def __init__(self, source: str):
        self.source = source
        self.key = bytes(RNG.randint(1, 255) for _ in range(32))

    def _deobf_helper(self) -> str:
        key_arr = ",".join(str(b) for b in self.key)
        seeds = ",".join(str(RNG.randint(0, 0xFFFFFFFF)) for _ in range(8))
        return (
            f"_0xkey=bytes([{key_arr}])\n"
            f"_0xseed=[{seeds}]\n"
            "def _0xdeobf(_0xs):\n"
            "    _0xb=bytes(int(x) for x in _0xs.split(','))\n"
            "    return bytes(c^_0xkey[i%len(_0xkey)] for i,c in enumerate(_0xb)).decode('utf-8')\n"
            "def _0xopaque():\n"
            "    _0xa=_0xseed[0];_0xb=_0xseed[1]\n"
            "    _0xc=(_0xa*_0xb)^(_0xa+_0xb)\n"
            "    _0xd=(_0xc>>3)|(_0xc<<29)\n"
            "    return (_0xd*_0xa)&0xffffffff==_0xseed[2]\n"
        )

    def run(self) -> str:
        tree = ast.parse(self.source)
        tree = NameMangler().run(tree)
        tree = StringHider(self.key).visit(tree)
        tree = OpaqueInjector().visit(tree)
        ast.fix_missing_locations(tree)
        body = ast.unparse(tree)
        return self._deobf_helper() + body


class CObfuscator:
    def __init__(self, c_source: str, n_junk_funcs: int = 2000,
                 n_junk_strings: int = 4000, n_junk_structs: int = 600,
                 split: int = 512, has_used_attr: bool = True,
                 has_pragma: bool = True, pad_bytes: int = 0):
        self.c = c_source
        self.n_junk_funcs = max(0, int(n_junk_funcs))
        self.n_junk_strings = max(0, int(n_junk_strings))
        self.n_junk_structs = max(0, int(n_junk_structs))
        self.split = max(0, int(split))
        self.has_used_attr = has_used_attr
        self.has_pragma = has_pragma
        self.pad_bytes = max(0, int(pad_bytes))
        self._junk_names: list[str] = []
        self._struct_names: list[str] = []

    def _attr_used(self) -> str:
        return "__attribute__((used))" if self.has_used_attr else ""

    def _attr_used_noinline(self) -> str:
        if self.has_used_attr:
            return "__attribute__((used,noinline))"
        return "__attribute__((noinline))"

    def _pragma_start(self) -> str:
        return "#pragma GCC push_options\n#pragma GCC optimize (\"O0\")\n" if self.has_pragma else ""

    def _pragma_end(self) -> str:
        return "#pragma GCC pop_options\n" if self.has_pragma else ""

    def _junk_globals(self, n: int) -> str:
        out = []
        attr = self._attr_used()
        for _ in range(n):
            nm = _rname("_jg_", 14)
            out.append(
                f"static volatile unsigned long {nm} "
                f"{attr} = 0x{RNG.randint(0, 0xFFFFFFFF):08X}UL;"
            )
        return "\n".join(out) + "\n"

    def _junk_structs(self, n: int) -> str:
        out = []
        self._struct_names = []
        for _ in range(n):
            nm = _rname("_js_", 12)
            self._struct_names.append(nm)
            fields = []
            nf = RNG.randint(6, 24)
            for _ in range(nf):
                f = _rname("_f_", 8)
                t = RNG.choice(["int", "long", "unsigned", "short", "char",
                                "double", "float", "void*", "long long",
                                "unsigned long", "unsigned char"])
                arr = ""
                if RNG.random() < 0.35:
                    arr = f"[{RNG.randint(2, 16)}]"
                fields.append(f"    {t} {f}{arr};")
            pad = RNG.randint(0, 128)
            if pad:
                fields.append(f"    char _pad_{_rname('p', 6)}[{pad}];")
            out.append(f"typedef struct {nm} {{\n" + "\n".join(fields) + f"\n}} {nm}_t;")
        return "\n".join(out) + "\n"

    def _junk_struct_instances(self) -> str:
        if not self._struct_names:
            return ""
        out = []
        inst_names = []
        attr = self._attr_used()
        for i, sname in enumerate(self._struct_names):
            inst = f"_ji_{i}_{_rname('s', 6)}"
            inst_names.append(inst)
            out.append(f"static {sname}_t {inst} {attr};")
        out.append(f"{self._attr_used_noinline()} unsigned long _junk_struct_touch(void) {{")
        out.append("    unsigned long _h = 0;")
        for inst in inst_names:
            out.append(f"    _h ^= sizeof({inst});")
            out.append(f"    _h = (_h * 31UL);")
        out.append("    return _h;")
        out.append("}")
        return "\n".join(out) + "\n"

    def _opaque_predicate(self) -> str:
        a = RNG.randint(0x100000, 0xFFFFFF)
        b = RNG.randint(0x100000, 0xFFFFFF)
        return f"(({a}UL * {b}UL + 7UL) == 0UL)"

    def _junk_func_named(self, name: str) -> str:
        n_locals = RNG.randint(16, 40)
        lines = [
            self._pragma_start(),
            self._attr_used_noinline(),
            f"static int {name}(int _x) {{",
            "    (void)_x;",
        ]
        for j in range(n_locals):
            lines.append(f"    volatile unsigned long _v{j} = 0x{RNG.randint(0, 0xFFFFFFFF):08X}UL;")
        for _ in range(RNG.randint(40, 90)):
            dst = f"_v{RNG.randrange(n_locals)}"
            a = f"_v{RNG.randrange(n_locals)}"
            b = RNG.choice([f"_v{RNG.randrange(n_locals)}", str(RNG.randint(1, 0xFFFF))])
            op = RNG.choice(["+", "-", "^", "|", "&", "*", ">>", "<<"])
            lines.append(f"    {dst} = ({a} {op} {b}) & 0xFFFFFFFFUL;")
            if RNG.random() < 0.35:
                lines.append(f"    if ({self._opaque_predicate()}) {{ {dst} ^= 0x{RNG.randint(0,0xFFFF):04X}; }}")
        lines.append("    return (int)(_v0 & 0x7FFFFFFF);")
        lines.append("}")
        lines.append(self._pragma_end())
        return "\n".join(lines)

    def _junk_functions(self, n: int) -> str:
        if n <= 0:
            return ""
        self._junk_names = []
        parts = []
        for i in range(n):
            name = _rname(f"_fn{i}_", 10)
            self._junk_names.append(name)
            parts.append(self._junk_func_named(name))
        attr = self._attr_used()
        table = f"static int (*const _junk_tab[])(int) {attr} = {{\n"
        table += ",\n".join(f"    {nm}" for nm in self._junk_names)
        table += "\n};\n"
        table += (
            f"{self._attr_used_noinline()} int _junk_run(unsigned long _s) {{\n"
            "    int _a = 0;\n"
            f"    unsigned long _n = _s % {len(self._junk_names)}UL;\n"
            f"    for (unsigned long _i = 0; _i < {len(self._junk_names)}UL; _i++) {{\n"
            "        _a ^= _junk_tab[_i](_a);\n"
            "        _a = (_a << 1) ^ (int)_i;\n"
            "    }\n"
            "    return _a ^ (int)_n;\n"
            "}\n"
        )
        return table + "\n" + "\n\n".join(parts)

    def _junk_strings(self, n: int) -> str:
        if n <= 0:
            return ""
        attr = self._attr_used()
        out = [f"static const char *_junk_strs[] {attr} = {{"]
        for _ in range(n):
            s = "".join(
                RNG.choice("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
                for _ in range(RNG.randint(32, 128))
            )
            out.append(f'    "{s}",')
        out.append("};")
        out.append(
            f"{self._attr_used_noinline()} unsigned long _junk_strhash(void) {{"
            "    unsigned long _h = 1469598103934665603UL;"
            f"    for (unsigned long _i = 0; _i < {n}UL; _i++) {{"
            "        const char *_p = _junk_strs[_i];"
            "        while (*_p) { _h ^= (unsigned char)*_p++; _h *= 1099511628211UL; }"
            "    }"
            "    return _h;"
            "}"
        )
        return "\n".join(out)

    def _pad_blob(self, n: int) -> str:
        if n <= 0:
            return ""
        attr = self._attr_used()
        lines = []
        lines.append(self._pragma_start())
        block = 8192
        total = n
        names = []
        while total > 0:
            sz = min(block, total)
            total -= sz
            nm = _rname("_pad_", 12)
            names.append(nm)
            lines.append(f"static const unsigned char {nm}[{sz}] {attr} = {{")
            row = []
            for _ in range(sz):
                row.append(f"0x{RNG.randint(0,255):02X}")
                if len(row) == 32:
                    lines.append("    " + ",".join(row) + ",")
                    row = []
            if row:
                lines.append("    " + ",".join(row) + ",")
            lines.append("};")
        lines.append(
            f"{self._attr_used_noinline()} unsigned long _pad_mix(void) {{"
            "    unsigned long _h = 0xC0FFEEUL;"
            "    volatile unsigned long _sink = 0;"
        )
        for nm in names:
            lines.append(f"    _sink += (volatile unsigned long){nm}[0];")
            lines.append(f"    _sink += (volatile unsigned long){nm}[sizeof({nm}) - 1];")
            lines.append(f"    _h = (_h ^ _sink) * 2654435761UL;")
            lines.append(f"    _h = (_h << 1) | (_h >> 31);")
        lines.append("    return _h ^ _sink;")
        lines.append("}")
        lines.append(self._pragma_end())
        return "\n".join(lines)

    _SPLIT_BAIL = re.compile(
        r"\b(return|goto|break|continue|setjmp|longjmp|va_start|va_end)\b"
    )

    def _flatten_c(self, text: str) -> str:
        if self.split <= 0:
            return text
        out_lines: list[str] = []
        i = 0
        src = text.split("\n")
        n = len(src)
        while i < n:
            line = src[i]
            m = re.match(
                r"^static\s+(?:void|int|long|unsigned|char|float|double|size_t)\s+"
                r"([A-Za-z_][A-Za-z0-9_]*)\s*\(void\)\s*\{\s*$",
                line,
            )
            if m and "PyInit" not in line and "__Pyx" not in line:
                depth = line.count("{") - line.count("}")
                j = i + 1
                body = []
                ok = True
                while j < n and depth > 0:
                    depth += src[j].count("{") - src[j].count("}")
                    if '"' in src[j] and src[j].count('"') % 2 != 0:
                        ok = False
                    if self._SPLIT_BAIL.search(src[j]):
                        ok = False
                    body.append(src[j])
                    j += 1
                if ok and depth == 0 and len(body) > self.split:
                    out_lines.extend(self._split_one_function(line, body))
                    i = j
                    continue
            out_lines.append(line)
            i += 1
        return "\n".join(out_lines)

    def _split_one_function(self, header: str, body: list[str]) -> list[str]:
        nmatch = re.search(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(\s*void\s*\)", header)
        if not nmatch:
            return [header] + body + ["}"]
        base = nmatch.group(1)
        prefix = header[: nmatch.start(1)]
        if "(" in prefix or ")" in prefix:
            return [header] + body + ["}"]
        ret_match = re.match(r"^(static\s+)(.*?)\s+[A-Za-z_]", header)
        if not ret_match:
            return [header] + body + ["}"]
        ret_type = ret_match.group(2).strip()
        if "*" in ret_type or "[" in ret_type or "(" in ret_type:
            return [header] + body + ["}"]
        if ret_type not in ("void", "int", "long", "unsigned", "char",
                            "float", "double", "size_t"):
            return [header] + body + ["}"]
        is_void = ret_type == "void"

        parts = max(2, len(body) // max(1, self.split))
        chunk = max(1, len(body) // parts)
        subs = []
        for k in range(parts):
            sub_body = body[k * chunk:(k + 1) * chunk] if k < parts - 1 else body[k * chunk:]
            sname = f"{base}_{k}_{_rname('s', 6)}"
            subs.append((sname, sub_body))

        out = []
        for sname, _ in subs:
            if is_void:
                out.append(f"static void {sname}(void);")
            else:
                out.append(f"static int {sname}(void);")
        out.append("")

        for sname, sub_body in subs:
            out.append(self._attr_used_noinline())
            if is_void:
                out.append(f"static void {sname}(void) {{")
                out.append("    volatile int _st = 0;")
                for ln in sub_body:
                    if RNG.random() < 0.25:
                        out.append("    if (" + self._opaque_predicate() + ") { _st += 1; }")
                    out.append("    " + ln)
                out.append("    (void)_st;")
                out.append("}")
            else:
                out.append(f"static int {sname}(void) {{")
                out.append("    volatile int _st = 0;")
                for ln in sub_body:
                    if RNG.random() < 0.25:
                        out.append("    if (" + self._opaque_predicate() + ") { _st += 1; }")
                    out.append("    " + ln)
                out.append("    return _st;")
                out.append("}")
            out.append("")

        out.append(header)
        out.append("{")
        if is_void:
            out.append("    volatile unsigned long _acc = 0xDEADBEEFUL;")
            for sname, _ in subs:
                out.append(f"    {sname}();")
                out.append(f"    _acc += (unsigned long)(sizeof(&{sname}));")
            out.append("    (void)_acc;")
            out.append("}")
        else:
            out.append("    volatile unsigned long _acc = 0xDEADBEEFUL;")
            for sname, _ in subs:
                out.append(f"    _acc += (unsigned long){sname}();")
                out.append(f"    if (_acc == 0x{RNG.randint(0,0xFFFFFFFF):08X}UL) _acc ^= {RNG.randint(1,0xFF)};")
            out.append("    return (int)(_acc & 0x7FFFFFFF);")
            out.append("}")
        return out

    def run(self) -> str:
        text = self.c
        text = self._flatten_c(text)

        header = []
        header.append("/* native payload */")
        header.append(self._junk_globals(max(128, self.n_junk_funcs // 16)))
        header.append(self._junk_structs(self.n_junk_structs))
        header.append(self._junk_struct_instances())
        if self.n_junk_funcs:
            header.append(self._junk_functions(self.n_junk_funcs))
        if self.n_junk_strings:
            header.append(self._junk_strings(self.n_junk_strings))
        if self.pad_bytes:
            header.append(self._pad_blob(self.pad_bytes))
        header.append("")
        header_text = "\n".join(header)

        idx = text.find("int main(")
        if idx == -1:
            idx = text.find("main(")
        if idx != -1:
            inject = header_text
            inject += "\n    (void)_junk_struct_touch();\n"
            if self._junk_names:
                inject += "    (void)_junk_run(0x1234UL);\n"
            if self.n_junk_strings:
                inject += "    (void)_junk_strhash();\n"
            if self.pad_bytes:
                inject += "    (void)_pad_mix();\n"
            text = text[:idx] + inject + text[idx:]
        else:
            text = header_text + "\n" + text
        return text


class CythonBuilder:
    def __init__(self, source_text: str, workdir: Path,
                 n_junk_funcs: int = 2000,
                 n_junk_strings: int = 4000,
                 n_junk_structs: int = 600,
                 split: int = 512,
                 pad_bytes: int = 0,
                 opt: str = "-O1", strip: bool = True,
                 cc_path: str | None = None):
        self.source_text = source_text
        self.workdir = workdir
        self.n_junk_funcs = n_junk_funcs
        self.n_junk_strings = n_junk_strings
        self.n_junk_structs = n_junk_structs
        self.split = split
        self.pad_bytes = pad_bytes
        self.opt = opt
        self.strip = strip
        self.cc_path = cc_path
        self.workdir.mkdir(parents=True, exist_ok=True)

    def _check(self):
        cython = shutil.which("cython") or shutil.which("cython3")
        if not cython:
            try:
                import Cython  # noqa
                cython = f"{sys.executable} -m cython"
            except ImportError:
                raise RuntimeError("Cython not found. Run: pip install cython")

        cc_spec = self.cc_path or os.environ.get("CC") or shutil.which("gcc") or shutil.which("clang")
        if not cc_spec:
            raise RuntimeError(
                "Compiler (GCC/Clang) not found. Run: pkg install gcc or apt-get install gcc"
            )
        cc_spec = _validate_gcc(cc_spec)

        return {"cython": cython, "cc": cc_spec}

    def _probe_attribute(self, cc: str, attr_body: str) -> bool:
        src = (
            f"__attribute__(({attr_body})) static int _probe_attr(void) {{ return 1; }}\n"
            "int main(void){return _probe_attr();}\n"
        )
        try:
            with tempfile.NamedTemporaryFile(suffix=".c", delete=False, mode="w") as f:
                f.write(src)
                tmp_src = f.name
            tmp_out = tmp_src + ".out"
            try:
                r = subprocess.run(
                    _cc_argv(cc) + ["-Werror=attributes", "-x", "c", tmp_src, "-o", tmp_out],
                    capture_output=True, text=True, timeout=30,
                )
                return r.returncode == 0
            finally:
                for p in (tmp_src, tmp_out):
                    try:
                        os.unlink(p)
                    except OSError:
                        pass
        except Exception:
            return False

    def _probe_pragma(self, cc: str) -> bool:
        src = (
            "#pragma GCC push_options\n"
            "#pragma GCC optimize (\"O0\")\n"
            "static int _probe_p(void) { return 1; }\n"
            "#pragma GCC pop_options\n"
            "int main(void){return _probe_p();}\n"
        )
        try:
            with tempfile.NamedTemporaryFile(suffix=".c", delete=False, mode="w") as f:
                f.write(src)
                tmp_src = f.name
            tmp_out = tmp_src + ".out"
            try:
                r = subprocess.run(
                    _cc_argv(cc) + ["-x", "c", tmp_src, "-o", tmp_out],
                    capture_output=True, text=True, timeout=30,
                )
                stderr = (r.stderr or "").lower()
                if "unknown pragma" in stderr or "ignoring" in stderr:
                    return False
                return r.returncode == 0
            finally:
                for p in (tmp_src, tmp_out):
                    try:
                        os.unlink(p)
                    except OSError:
                        pass
        except Exception:
            return False

    def prepare(self):
        tools = self._check()
        pyx = self.workdir / "_obf.pyx"
        pyx.write_text(self.source_text, encoding="utf-8")
        subprocess.run(
            shlex.split(tools["cython"]) + ["-3", "--embed", "-o",
                                            str(self.workdir / "_obf.c"), str(pyx)],
            check=True, cwd=str(self.workdir),
        )
        c_file = self.workdir / "_obf.c"
        if not c_file.exists():
            raise RuntimeError("Cython did not produce .c")
        raw_c = c_file.read_text(encoding="utf-8", errors="ignore")
        log(f"[*] Cython C: {raw_c.count(chr(10)):,} lines, {len(raw_c):,} bytes")

        cc = tools["cc"]
        has_used = self._probe_attribute(cc, "used")
        has_pragma = self._probe_pragma(cc)
        log(f"[*] Attr used={has_used} pragma-O0={has_pragma}")

        obf_c = self.workdir / "_obf.obf.c"
        obf_text = CObfuscator(
            raw_c,
            n_junk_funcs=self.n_junk_funcs,
            n_junk_strings=self.n_junk_strings,
            n_junk_structs=self.n_junk_structs,
            split=self.split,
            has_used_attr=has_used,
            has_pragma=has_pragma,
            pad_bytes=self.pad_bytes,
        ).run()
        obf_c.write_text(obf_text, encoding="utf-8")
        log(f"[*] Obfuscated C: {obf_text.count(chr(10)):,} lines, {len(obf_text):,} bytes")

        self._tools = tools
        self._has_used = has_used
        self._has_pragma = has_pragma
        self._obf_c = obf_c
        return tools

    def build_from_prepared(self, tools, obf_c: Path) -> Path:
        import sysconfig
        inc = sysconfig.get_path("include")
        lib_dir = sysconfig.get_config_var("LIBDIR") or ""
        lib_name = sysconfig.get_config_var("LDLIBRARY") or ""
        py_cfg = shutil.which("python3-config") or shutil.which("python-config")
        if py_cfg:
            incs = subprocess.run([py_cfg, "--includes"], capture_output=True,
                                  text=True, check=True).stdout.split()
            ld_res = subprocess.run([py_cfg, "--ldflags", "--embed"], capture_output=True, text=True)
            if ld_res.returncode == 0:
                libs = ld_res.stdout.split()
                libs += subprocess.run([py_cfg, "--libs", "--embed"], capture_output=True,
                                       text=True, check=True).stdout.split()
            else:
                libs = subprocess.run([py_cfg, "--ldflags"], capture_output=True,
                                      text=True, check=True).stdout.split()
                libs += subprocess.run([py_cfg, "--libs"], capture_output=True,
                                       text=True, check=True).stdout.split()
        else:
            incs = [f"-I{inc}"]
            libs = []
            if lib_dir and lib_name:
                lib = lib_name.replace("lib", "").replace(".so", "").replace(".dylib", "")
                libs = [f"-L{lib_dir}", f"-l{lib}", f"-Wl,-rpath,{lib_dir}"]

        out_bin = self.workdir / ("_obf.exe" if sys.platform == "win32" else "_obf")
        cc = tools["cc"]
        android = _is_android()

        base_flags: list[str] = [self.opt]
        if sys.platform != "win32":
            if android:
                base_flags += ["-fPIE", "-fPIC", "-pie", "-fvisibility=hidden"]
            else:
                base_flags += ["-fPIC", "-fvisibility=hidden"]

        candidate_flags = [
            "-fno-inline",
            "-fno-inline-functions",
            "-fno-inline-functions-called-once",
            "-fno-omit-frame-pointer",
            "-fno-optimize-sibling-calls",
            "-fno-tree-vectorize",
            "-fno-tree-slp-vectorize",
            "-fno-tree-loop-vectorize",
            "-fno-guess-branch-probability",
            "-fno-reorder-blocks-and-partition",
            "-fno-reorder-functions",
            "-fno-align-functions",
            "-fno-align-loops",
            "-fno-align-jumps",
            "-falign-functions=64",
            "-falign-loops=64",
            "-falign-jumps=64",
            "-fno-merge-constants",
            "-fno-merge-all-constants",
            "-fno-common",
            "-fno-thread-jumps",
            "-fno-crossjumping",
            "-fno-if-conversion",
            "-fno-if-conversion2",
            "-fno-tree-dominator-opts",
            "-fno-tree-fre",
            "-fno-tree-pre",
            "-fno-tree-ccp",
            "-fno-tree-dce",
            "-fno-tree-dse",
            "-fno-tree-forwprop",
            "-fno-tree-sink",
            "-fno-tree-ter",
            "-fno-tree-switch-conversion",
            "-fno-ssa-phiopt",
            "-fno-strict-aliasing",
            "-fno-strict-overflow",
            "-fno-lto",
            "-fno-toplevel-reorder",
            "-fno-section-anchors",
            "-funwind-tables",
        ]

        gcc_flags = filter_supported_flags(cc, candidate_flags, base=tuple(base_flags))

        cc_cmd = _cc_argv(cc) + base_flags + gcc_flags
        if self.strip:
            cc_cmd.append("-s")
        cc_cmd += [str(obf_c), "-o", str(out_bin)] + incs + libs + ["-lm"]

        log(f"[*] CC: ({cc}) android={android}")
        subprocess.run(cc_cmd, check=True, cwd=str(self.workdir))

        if self.strip and sys.platform != "win32":
            strip = shutil.which("strip")
            if strip:
                subprocess.run([strip, str(out_bin)], check=False)
        return out_bin


def _safe_key(name: str) -> str:
    if not name or len(name) > MAX_BUNDLE_KEY:
        raise ValueError(f"bad bundle key length: {name!r}")
    if name.startswith("/") or ".." in name.split("/"):
        raise ValueError(f"unsafe bundle key: {name!r}")
    if "\x00" in name or "\\" in name:
        raise ValueError(f"unsafe bundle key: {name!r}")
    if not re.fullmatch(r"[A-Za-z0-9._\-/]+", name):
        raise ValueError(f"unsafe bundle key: {name!r}")
    return name


class Bundle:
    def __init__(self):
        self.entries: dict[str, bytes] = {}

    def add(self, name: str, data: bytes):
        name = _safe_key(name)
        if "." not in name:
            raise ValueError(f"bad bundle key: {name!r}")
        self.entries[name] = data

    def to_tar_xz(self) -> bytes:
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:xz", preset=9) as tf:
            for name, data in self.entries.items():
                info = tarfile.TarInfo(name)
                info.size = len(data)
                info.mode = 0o755
                info.uid = 0
                info.gid = 0
                info.uname = ""
                info.gname = ""
                info.mtime = 0
                tf.addfile(info, io.BytesIO(data))
        return buf.getvalue()


_LAUNCHER_TEMPLATE = r'''# -*- coding: utf-8 -*-
S = "%%TMPNAME%%"
X = (
%%PAYLOAD%%
)
_SHA = "%%SHA256%%"
_PKX = bytes.fromhex("%%PKX%%")
_PKB = bytes.fromhex("%%PKB%%")
_HKX = bytes.fromhex("%%HKX%%")
_HKB = bytes.fromhex("%%HKB%%")

_EXPIRY = "%%EXPIRY%%"
_EXPIRY_MSG = "%%EXPIRY_MSG%%"
_PW_HASH = "%%PW_HASH%%"

import os, sys, base64 as b, io as i, tarfile as t, hashlib as h, hmac as hm, tempfile as tf, platform as p, stat as st, errno as e


def _pdk():
    return bytes(c ^ _PKX[i % len(_PKX)] for i, c in enumerate(_PKB))


def _hdk():
    return bytes(c ^ _HKX[i % len(_HKX)] for i, c in enumerate(_HKB))


def _n():
    if sys.platform == "win32":
        return "win"
    m = p.machine().lower()
    if m in ("x86_64", "amd64"):
        return "x86_64"
    if m in ("aarch64", "arm64"):
        return "arm64"
    if m in ("armv7l", "armv8l", "armv7", "armv6l", "arm", "arm32"):
        return "arm32"
    if m in ("i386", "i686", "x86"):
        return "x86"
    sys.exit("[X] unsupported arch: " + m)


def _pick(names, arch):
    pv = "%d.%d" % (sys.version_info[0], sys.version_info[1])
    # 1. Exact match for current python version + architecture
    if arch == "win":
        for c in ("%s.win.exe" % pv, "%s.win" % pv, "%s.x86_64.exe" % pv):
            if c in names:
                return c
    want = "%s.%s" % (pv, arch)
    if want in names:
        return want
    for x in names:
        if x.startswith(pv + ".") and (x.endswith("." + arch) or x.endswith("." + arch + ".exe")):
            return x
    # 2. Architecture match for any python version in bundle
    for x in names:
        if arch == "win" and "win" in x:
            return x
        if x.endswith("." + arch) or x.endswith("." + arch + ".exe") or ("." + arch + "." in x):
            return x
    # 3. Flexible prefix / substring match for architecture
    for x in names:
        if arch in x:
            return x
    # 4. Universal fallback: try any binary available in bundle
    if names:
        return names[0]
    return None


def _verify(raw, sha_hex, hmac_key, hmac_hex):
    if h.sha256(raw).hexdigest() != sha_hex:
        sys.exit("[X] payload integrity check failed")
    if hmac_key:
        calc = hm.new(hmac_key, raw, h.sha256).hexdigest()
        if not hm.compare_digest(calc, hmac_hex):
            sys.exit("[X] payload authentication failed")


def _entry(d, name):
    with t.open(fileobj=i.BytesIO(d), mode="r:xz") as f:
        try:
            m = f.getmember(name)
        except KeyError:
            return None
        if not m.isfile():
            return None
        ef = f.extractfile(m)
        if ef is None:
            return None
        return ef.read()


def _rl(data, is_win=False):
    # Ensure TMPDIR on Android points to writable executable directory
    prefix_tmp = "/data/data/com.termux/files/usr/tmp"
    if not os.environ.get("TMPDIR") and os.path.exists(prefix_tmp):
        os.environ["TMPDIR"] = prefix_tmp

    td = tf.mkdtemp(prefix="pyp_")
    try:
        os.chmod(td, 0o700)
    except OSError:
        pass

    base = os.path.basename(S) or "pyp_run"
    base = "".join(c for c in base if c.isalnum() or c in "._-") or "pyp_run"
    if is_win and not base.lower().endswith(".exe"):
        base += ".exe"

    pp = os.path.join(td, base)
    fd = None
    flags = os.O_RDWR | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC

    try:
        fd = os.open(pp, flags, 0o700)
        with os.fdopen(fd, "wb") as f:
            fd = None
            f.write(data)
        os.chmod(pp, 0o700)
    except Exception as exc:
        if fd is not None:
            try: os.close(fd)
            except OSError: pass
        try: os.unlink(pp)
        except OSError: pass
        try: os.rmdir(td)
        except OSError: pass
        sys.exit("[X] failed to unpack binary: " + str(exc))

    if is_win or not hasattr(os, "fork"):
        # Windows or platforms without fork: use subprocess.call & cleanup
        import subprocess as _sp
        ret_code = 1
        try:
            ret_code = _sp.call([pp] + sys.argv[1:])
        finally:
            try:
                os.unlink(pp)
            except OSError:
                pass
            try:
                os.rmdir(td)
            except OSError:
                pass
        sys.exit(ret_code)
    else:
        # Unix/Linux/Android: fork child to execute; parent cleans up temp files!
        pid = os.fork()
        if pid == 0:
            # Child process: replace image with unpacked binary
            try:
                os.execv(pp, [base] + sys.argv[1:])
            except Exception as _e:
                sys.exit(127)
        else:
            # Parent process: wait for child exit, then clean temp binary & dir
            exit_code = 0
            try:
                _, status = os.waitpid(pid, 0)
                if hasattr(os, "waitstatus_to_exitcode"):
                    exit_code = os.waitstatus_to_exitcode(status)
                else:
                    exit_code = (status >> 8) if os.WIFEXITED(status) else 1
            except Exception:
                exit_code = 1
            finally:
                try:
                    os.unlink(pp)
                except OSError:
                    pass
                try:
                    os.rmdir(td)
                except OSError:
                    pass
            sys.exit(exit_code)


def _m():
    try:
        # 1. Check Expiration gate
        if _EXPIRY:
            import datetime as _dt
            try:
                _exp_ts = int(_EXPIRY) if _EXPIRY.isdigit() else int(_dt.datetime.fromisoformat(_EXPIRY).timestamp())
                if int(_dt.datetime.now().timestamp()) >= _exp_ts:
                    msg = _EXPIRY_MSG or "[X] Script execution expired. Please renew your license."
                    sys.exit(msg)
            except ValueError:
                pass

        # 2. Check Password gate
        if _PW_HASH:
            import getpass as _gp
            try:
                _inp = _gp.getpass("[?] Enter password to run script: ")
            except (KeyboardInterrupt, EOFError):
                sys.exit(130)
            if h.sha256(_inp.encode("utf-8")).hexdigest() != _PW_HASH:
                sys.exit("[!] Access denied: Invalid password.")

        # 3. Payload unpacking & integrity check
        raw = b.b85decode("".join(X).encode())
        pk = _pdk()
        d = bytes(c ^ pk[i % len(pk)] for i, c in enumerate(raw))
        hk = _hdk()
        _verify(d, _SHA, hk, "%%HMAC_HEX%%")
        arch = _n()
        is_win = (arch == "win")
        with t.open(fileobj=i.BytesIO(d), mode="r:xz") as f:
            names = [m.name for m in f.getmembers() if m.isfile()]
        name = _pick(names, arch)
        if name is None and names:
            name = names[0]
        if name is None:
            pyver = "%d.%d" % (sys.version_info[0], sys.version_info[1])
            sys.exit(f"[X] No compatible binary found for Python {pyver} ({arch}). Available in bundle: {names}")
        payload = _entry(d, name)
        if payload is None:
            sys.exit("[X] payload entry unreadable")
        _rl(payload, is_win=is_win)
    except SystemExit:
        raise
    except Exception as ex:
        print("[X] " + str(ex), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    _m()
'''


class LauncherWriter:
    @classmethod
    def write(
        cls,
        bundle_bytes: bytes,
        out_path: Path,
        tmpname: str,
        chunk: int = CHUNK,
        expiry: str | None = None,
        expiry_msg: str | None = None,
        password: str | None = None,
    ):
        if len(bundle_bytes) > MAX_LAUNCHER_BYTES:
            raise RuntimeError(f"bundle too large: {len(bundle_bytes)} bytes")

        payload_key = secrets.token_bytes(32)
        xored = bytes(b ^ payload_key[i % len(payload_key)]
                      for i, b in enumerate(bundle_bytes))
        payload = base64.b85encode(xored).decode("ascii")

        key_xor = secrets.token_bytes(32)
        key_obf = bytes(k ^ key_xor[i % len(key_xor)]
                        for i, k in enumerate(payload_key))

        hmac_key = secrets.token_bytes(32)
        hmac_hex = hmac.new(hmac_key, bundle_bytes, hashlib.sha256).hexdigest()

        hmac_key_xor = secrets.token_bytes(32)
        hmac_key_obf = bytes(k ^ hmac_key_xor[i % len(hmac_key_xor)]
                             for i, k in enumerate(hmac_key))

        chunks = [payload[k:k + chunk] for k in range(0, len(payload), chunk)]
        payload_block = "\n".join(f'    "{c}"' for c in chunks)

        sha_hex = hashlib.sha256(bundle_bytes).hexdigest()
        safe_tmp = "".join(c for c in tmpname if c.isalnum() or c in "._-") or "pyp_run"

        # Prepare expiry timestamp & password hash strings
        exp_val = ""
        if expiry:
            try:
                exp_dt = _parse_datetime(expiry)
                exp_val = str(int(exp_dt.timestamp()))
            except Exception:
                exp_val = str(expiry)

        pw_hash_val = ""
        if password:
            pw_hash_val = hashlib.sha256(password.encode("utf-8")).hexdigest()

        text = _LAUNCHER_TEMPLATE
        text = text.replace("%%PAYLOAD%%", payload_block)
        text = text.replace("%%SHA256%%", sha_hex)
        text = text.replace("%%PKX%%", key_xor.hex())
        text = text.replace("%%PKB%%", key_obf.hex())
        text = text.replace("%%HKX%%", hmac_key_xor.hex())
        text = text.replace("%%HKB%%", hmac_key_obf.hex())
        text = text.replace("%%HMAC_HEX%%", hmac_hex)
        text = text.replace("%%TMPNAME%%", safe_tmp)
        text = text.replace("%%EXPIRY%%", exp_val)
        text = text.replace("%%EXPIRY_MSG%%", (expiry_msg or "").replace('"', '\\"'))
        text = text.replace("%%PW_HASH%%", pw_hash_val)

        compile(text, str(out_path), "exec")
        out_path.write_text(text, encoding="utf-8", newline="\n")
        try:
            os.chmod(out_path, 0o700)
        except OSError:
            pass
        return len(chunks)


def write_wrapper(out_path: Path):
    wrapper = out_path.with_name(out_path.stem + "_main_out.py")
    wrapper.write_text(
        "import runpy, sys, pathlib\n"
        f"_p = pathlib.Path(__file__).with_name({out_path.name!r})\n"
        "sys.argv[0] = str(_p)\n"
        "runpy.run_path(str(_p), run_name='__main__')\n",
        encoding="utf-8",
    )
    return wrapper


def _extract_launcher_assigns(src: str) -> dict:
    tree = ast.parse(src)
    out: dict = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for tgt in node.targets:
                if isinstance(tgt, ast.Name):
                    if tgt.id in ("X", "_SHA", "_PKX", "_PKB", "_EXPIRY", "_PW_HASH"):
                        try:
                            out[tgt.id] = ast.literal_eval(node.value)
                        except Exception:
                            pass
    return out


def verify_launcher(out_path: Path) -> list[str]:
    src = out_path.read_text(encoding="utf-8")
    vals = _extract_launcher_assigns(src)
    if "X" not in vals or "_SHA" not in vals:
        raise RuntimeError("launcher missing X or _SHA")
    if "_PKX" not in vals or "_PKB" not in vals:
        raise RuntimeError("launcher missing payload key material")

    x_val = vals["X"]
    sha_val = vals["_SHA"]
    pkx = vals["_PKX"]
    pkb = vals["_PKB"]

    if isinstance(pkx, str):
        pkx = bytes.fromhex(pkx)
    if isinstance(pkb, str):
        pkb = bytes.fromhex(pkb)

    pk = bytes(c ^ pkx[i % len(pkx)] for i, c in enumerate(pkb))

    if isinstance(x_val, str):
        payload = x_val
    else:
        payload = "".join(x_val)
    if len(payload) > MAX_LAUNCHER_BYTES * 2:
        raise RuntimeError("payload too large to verify")

    raw = base64.b85decode(payload.encode())
    data = bytes(c ^ pk[i % len(pk)] for i, c in enumerate(raw))
    if hashlib.sha256(data).hexdigest() != sha_val:
        raise RuntimeError("sha256 mismatch")

    with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as f:
        names = [m.name for m in f.getmembers() if m.isfile()]
    for nm in names:
        if nm.startswith("/") or ".." in nm.split("/"):
            raise RuntimeError(f"unsafe entry in bundle: {nm!r}")
    return names


def current_arch() -> str:
    if sys.platform == "win32":
        return "win"
    mach = platform.machine().lower()
    if mach in ("x86_64", "amd64"):
        return "x86_64"
    if mach in ("aarch64", "arm64"):
        return "arm64"
    if mach in ("armv7l", "armv8l", "armv7", "armv6l", "arm", "arm32"):
        return "arm32"
    if mach in ("i386", "i686", "x86"):
        return "x86"
    return mach


def find_gcc() -> str:
    env_cc = os.environ.get("CC")
    if env_cc:
        try:
            return _validate_gcc(env_cc)
        except ValueError as exc:
            warn(f"ignoring CC env var: {exc}")
    for cand in ("gcc", "gcc-14", "gcc-13", "gcc-12", "gcc-11", "gcc-10", "clang"):
        p = shutil.which(cand)
        if p:
            return p
    sys.exit(
        "[!] GCC/Clang compiler not found.\n"
        "    Install with: pkg install gcc or apt install gcc"
    )


def parse_args():
    ap = argparse.ArgumentParser(prog="enc10.py", description="PyEncrypt Multi-Version Python Native Compiler & Packager")
    ap.add_argument("source", help="Source Python (.py) file to encode")
    ap.add_argument("-o", "--output", default=None, help="Output file path")
    ap.add_argument("-y", "--yes", action="store_true", help="Overwrite existing output without prompt")
    ap.add_argument("-q", "--quiet", action="store_true", help="Suppress informational messages")
    ap.add_argument("--check", action="store_true", help="Perform verification check after packing")
    ap.add_argument("--tmpname", default=TEMP_NAME, help="Temporary binary execution filename")
    ap.add_argument("--pyver", default=None, choices=PY_VERSIONS, help="Target Python version label")
    ap.add_argument("--add-binary", action="append", default=[], metavar="KEY=PATH", help="Manually attach extra binary into bundle")
    ap.add_argument("--chunk", type=int, default=CHUNK, help="Base85 chunk characters per line")
    ap.add_argument("--c-junk", type=int, default=2000, help="Number of junk C functions to inject")
    ap.add_argument("--junk-strings", type=int, default=4000, help="Number of junk C strings to inject")
    ap.add_argument("--junk-structs", type=int, default=600, help="Number of junk C structs to inject")
    ap.add_argument("--split", type=int, default=512, help="Split threshold for large C functions")
    ap.add_argument("--pad-bytes", type=int, default=None, help="Explicit padding bytes")
    ap.add_argument("--target-kb", type=int, default=800, help="Target minimum size in KB")
    ap.add_argument("--opt", default="-O1", choices=["-O0", "-O1", "-O2", "-O3"], help="GCC optimization level")
    ap.add_argument("--no-strip", action="store_true", help="Do not strip native binary symbols")
    ap.add_argument("--gcc", default=None, help="Custom path to GCC compiler")

    # Multi-Version & Vault flags
    ap.add_argument("--vault", default=None, metavar="DIR", help="Use pre-built binaries from DIR instead of compiling")
    ap.add_argument("--targets", default="3.11,3.12,3.13,3.14", help="Comma-separated Python versions to bundle (e.g. '3.11,3.12,3.13,3.14')")
    ap.add_argument("--arches", default="arm64,arm32,win", help="Comma-separated architectures to bundle (e.g. 'arm64,arm32,win,x86_64')")
    ap.add_argument("--expiry", default=None, help="Embedded expiration datetime (e.g. '2026-12-31 23:59:59')")
    ap.add_argument("--expiry-msg", default=None, help="Message to display upon expiration")
    ap.add_argument("--password", default=None, help="Plaintext password required to run")
    ap.add_argument("--no-inject", action="store_true", help="Skip protection injection inside source code")
    ap.add_argument("--build-only", action="store_true", help="Build single native binary and output directly (for CI vault builder)")

    return ap.parse_args()


def _read_source(path: Path) -> str:
    if path.stat().st_size > MAX_SOURCE:
        sys.exit(f"[!] Source too large: {path}")
    return path.read_text(encoding="utf-8")


def _add_binary_entry(spec: str, bundle: Bundle):
    key, sep, path_s = spec.partition("=")
    if not sep:
        sys.exit(f"[!] Bad --add-binary: {spec}")
    key = key.strip()
    try:
        key = _safe_key(key)
    except ValueError as exc:
        sys.exit(f"[!] {exc}")
    if "." not in key:
        sys.exit(f"[!] --add-binary key must contain a dot: {key!r}")
    p = Path(path_s).expanduser().resolve()
    if not p.is_file():
        sys.exit(f"[!] Not a file: {p}")
    sz = p.stat().st_size
    if sz > MAX_ADD_BINARY:
        sys.exit(f"[!] --add-binary file too large: {sz} bytes")
    bundle.add(key, p.read_bytes())


def load_from_vault(vault_dir: Path, targets: list[str], arches: list[str]) -> Bundle:
    """
    Loads pre-built binaries from vault_dir matching requested Python targets and architectures.
    Looks for files named:
      {pyver}.{arch}
      {pyver}.{arch}.exe
      {pyver}.win.exe (if arch is 'win')
    """
    if not vault_dir.is_dir():
        sys.exit(f"[!] Vault directory not found: {vault_dir}")

    bundle = Bundle()
    found_count = 0

    log(f"[*] Loading vault binaries from: {vault_dir}")
    log(f"[*] Requested Targets : {targets}")
    log(f"[*] Requested Arches  : {arches}")

    for py in targets:
        for arch in arches:
            candidates: list[str] = []
            if arch == "win":
                candidates = [f"{py}.win.exe", f"{py}.win", f"{py}.x86_64.exe"]
            else:
                candidates = [f"{py}.{arch}", f"{py}.{arch}.bin", f"{py}.{arch}.so"]

            matched_file = None
            matched_key = None
            for cand in candidates:
                cand_path = vault_dir / cand
                if cand_path.is_file():
                    matched_file = cand_path
                    matched_key = cand
                    break

            if matched_file:
                data = matched_file.read_bytes()
                bundle.add(matched_key, data)
                found_count += 1
                log(f"    [+] Bundled: {matched_key} ({len(data):,} bytes)")
            else:
                warn(f"Vault missing binary for {py}.{arch} (tried: {candidates})")

    if found_count == 0:
        # Fallback: scan vault_dir for ANY available binaries and bundle them
        all_binaries = [f for f in vault_dir.iterdir() if f.is_file() and not f.name.startswith('.')]
        if all_binaries:
            warn(f"Requested targets {targets} ({arches}) not found in vault. Including available vault binaries as fallback.")
            for bf in all_binaries:
                data = bf.read_bytes()
                bundle.add(bf.name, data)
                found_count += 1
                log(f"    [+] Fallback bundled: {bf.name} ({len(data):,} bytes)")
        else:
            sys.exit(f"[!] No matching vault binaries found in {vault_dir} for requested targets!")

    return bundle


def main():
    global QUIET
    args = parse_args()
    QUIET = args.quiet
    real_pyver = derive_pyver()
    py_label = args.pyver or real_pyver

    src = Path(args.source).expanduser().resolve()
    if not src.is_file() or src.suffix.lower() != ".py":
        sys.exit(f"[!] Not a .py file: {src}")

    if args.output:
        out = Path(args.output).expanduser().resolve()
    else:
        out = (src.parent / (src.stem + "_enc10.py")).resolve()

    if out == src and not args.build_only:
        sys.exit("[!] Output cannot overwrite input")
    if out.exists() and not args.yes and not args.build_only:
        try:
            ans = input(f"[?] Overwrite {out}? [y/N]: ").strip().lower()
        except (EOFError, KeyboardInterrupt):
            sys.exit(130)
        if ans != "y":
            sys.exit("Cancelled.")

    chunk = max(4, int(args.chunk))
    gcc_path = None
    if not args.vault:
        gcc_found = args.gcc or find_gcc()
        try:
            gcc_path = _validate_gcc(gcc_found)
        except ValueError as exc:
            sys.exit(f"[!] {exc}")

    target_bytes = max(1, int(args.target_kb)) * 1024
    manual_pad = args.pad_bytes

    # 1. Protection Injection
    source_text = _read_source(src)
    if not args.no_inject and (args.expiry or args.password):
        log("[*] Injecting security protections into source...")
        source_text = inject_into_text(
            source_code=source_text,
            expiry=args.expiry,
            expiry_msg=args.expiry_msg,
            password=args.password,
        )

    # 2. Build-only Mode (Used for CI Vault Creation)
    if args.build_only:
        log(f"[*] Mode: --build-only (Compiling native binary for Python {real_pyver} on {current_arch()})")
        obf_text = ASTObfuscator(source_text).run()
        with tempfile.TemporaryDirectory(prefix="pyp_build_") as td:
            work = Path(td) / "build"
            builder = CythonBuilder(
                obf_text, work,
                n_junk_funcs=args.c_junk,
                n_junk_strings=args.junk_strings,
                n_junk_structs=args.junk_structs,
                split=args.split,
                pad_bytes=0,
                opt=args.opt,
                strip=not args.no_strip,
                cc_path=gcc_path,
            )
            builder.prepare()
            binary = builder.build_from_prepared(builder._tools, builder._obf_c)
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(binary, out)
            try:
                os.chmod(out, 0o755)
            except OSError:
                pass
            log(f"[+] Native binary written to: {out} ({out.stat().st_size:,} bytes)")
        return

    # 3. Vault Packaging Mode vs Live Compilation Mode
    if args.vault:
        vault_dir = Path(args.vault).expanduser().resolve()
        targets = [t.strip() for t in args.targets.split(",") if t.strip()]
        arches = [a.strip() for a in args.arches.split(",") if a.strip()]

        bundle = load_from_vault(vault_dir, targets, arches)
        for spec in args.add_binary:
            _add_binary_entry(spec, bundle)

        tar_bytes = bundle.to_tar_xz()
        bundle_size = len(tar_bytes)
        log(f"[+] Vault bundle created: {bundle_size:,} bytes with {len(bundle.entries)} targets")

    else:
        # Standard Single-Version Native Compilation Mode
        if args.pyver and args.pyver != real_pyver:
            warn(f"--pyver {args.pyver} differs from interpreter {real_pyver}.")

        log(f"[*] Source       : {src}")
        log(f"[*] Output       : {out}")
        log(f"[*] PyVer        : {real_pyver} (label: {py_label})")
        log(f"[*] Opt          : {args.opt}  strip={not args.no_strip}")
        log(f"[*] CC           : {gcc_path}")

        obf_text = ASTObfuscator(source_text).run()

        with tempfile.TemporaryDirectory(prefix="pyp_") as td:
            work = Path(td) / "build"
            try:
                os.chmod(td, 0o700)
            except OSError:
                pass

            def make_bundle(pad_amount: int):
                b = Bundle()
                builder = CythonBuilder(
                    obf_text, work,
                    n_junk_funcs=args.c_junk,
                    n_junk_strings=args.junk_strings,
                    n_junk_structs=args.junk_structs,
                    split=args.split,
                    pad_bytes=pad_amount,
                    opt=args.opt,
                    strip=not args.no_strip,
                    cc_path=gcc_path,
                )
                builder.prepare()
                binary = builder.build_from_prepared(builder._tools, builder._obf_c)
                data = binary.read_bytes()
                key_name = f"{py_label}.{current_arch()}"
                if sys.platform == "win32" and not key_name.endswith(".exe"):
                    key_name += ".exe"
                b.add(key_name, data)
                for spec in args.add_binary:
                    _add_binary_entry(spec, b)
                tb = b.to_tar_xz()
                return len(data), len(tb), b

            log("[*] Compiling native binary with GCC/Cython ...")
            try:
                bin_size, bundle_size, bundle = make_bundle(manual_pad or 0)
            except subprocess.CalledProcessError as exc:
                sys.exit(f"[!] Build failed: {exc}")
            except RuntimeError as exc:
                sys.exit(f"[!] {exc}")

            log(f"[+] Binary: {bin_size:,} bytes")
            log(f"[+] Bundle: {bundle_size:,} bytes ({len(bundle.entries)} entries)")

            if manual_pad is None:
                estimated_launcher = bundle_size * 5 // 4 + 4096
                if estimated_launcher < target_bytes:
                    needed_launcher = target_bytes - estimated_launcher
                    needed_bundle = needed_launcher * 4 // 5
                    pad = needed_bundle + 128 * 1024
                    log(f"[*] Auto pad: bundle {bundle_size:,} -> need +{needed_bundle:,} (pad={pad:,})")
                    try:
                        bin_size, bundle_size, bundle = make_bundle(pad)
                    except Exception as exc:
                        warn(f"Padding rebuild skipped: {exc}")

    # 4. Generate Launcher File
    tar_bytes = bundle.to_tar_xz()
    n_lines = LauncherWriter.write(
        bundle_bytes=tar_bytes,
        out_path=out,
        tmpname=args.tmpname,
        chunk=chunk,
        expiry=args.expiry,
        expiry_msg=args.expiry_msg,
        password=args.password,
    )
    wrapper = write_wrapper(out)
    final_size = out.stat().st_size
    log(f"[+] Launcher: {out}  ({n_lines:,} lines, {final_size:,} bytes / {final_size/1024:.1f} KB)")
    log(f"[+] Wrapper : {wrapper}")

    if args.check:
        try:
            names = verify_launcher(out)
            log(f"[+] Self-test passed! Bundle contains: {names}")
        except Exception as exc:
            sys.exit(f"[!] Self-test failed: {exc}")

    log("[+] Encoding completed successfully.")


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print()
        sys.exit(130)
