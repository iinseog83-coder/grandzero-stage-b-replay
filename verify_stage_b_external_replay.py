#!/usr/bin/env python3
"""
GRANDZERO Ω — Stage B (Minimal 2-Cell Transport) Hardened External Replay Verifier
==================================================================================
Enforces a 7-boolean fail-closed conjunction (`ExternalReplayPass`):
  1. `pre_pins_ok`        : Fail-fast ZIP size + SHA-256 + 16/16 internal file pins + no `.lake`
  2. `stage_a_lineage_ok` : All 6 vendored `StageA` library files match Stage A Final Closure pins
  3. `exact_4331`         : Exact Lean 4.33.1 (`commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6`)
  4. `clean_build_pass`   : Cold `lake build` exit code 0 in isolated temporary directory
  5. `audit_vectors_pass` : `lake exe stage_b_audit` exit code 0 + field-by-field match on
                            all 6 `VECTOR|ID=TB-01..TB-06` rows + 2 `EXTRA|...` rows + banner
  6. `axiom_audit_pass`   : `#check` & `#print axioms` on all 39 `GrandZero.StageB` theorems
                            using ONLY `{propext, Classical.choice, Quot.sound}` (multi-line safe)
  7. `source_identity_pass`: Post-build 16/16 source files + original ZIP SHA-256 unchanged
"""

import datetime
import hashlib
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE_NAME = "GRANDZERO_STAGE_B_2CELL_Q0_CLEANROOM_SOURCE_ARCHIVE.zip"
EXPECTED_ARCHIVE_SIZE = 74318
EXPECTED_ARCHIVE_SHA256 = "ca8d9bd2383648c625eac044aefaade01b53c442fc8238fec7f306bbf72609db"
EXPECTED_LEAN_VERSION_SUBSTR = "4.33.1"
EXPECTED_LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

STAGE_A_FROZEN_LIB_PINS = {
    "StageA.lean": "15592e37e2bf4db61de644e33ab8c2d69ce20949021401996c9e3495b3b586fb",
    "StageA/Q0SyntaxAndUnits.lean": "04ec42ab65c6db2192c7bc5b04010c840f5d61c1e1abdc49f938fe6a645ad807",
    "StageA/Q0PartialSemantics.lean": "3a4e83073c7b2633f86d24dc67bb8b8f9c6731a0d73d09aa35c8fb9478c90469",
    "StageA/Q0ValidTape.lean": "9bc851eb9d938972caac2e77af9d1ecf41009393fc2ff43e37b4535ccd06eade",
    "StageA/Q0GuardedReflection.lean": "aad43e6c1dceeec4bea83781a76b77ccf38926a52003dea296d08f3517035fc9",
    "StageA/Q0BipolarKernel.lean": "bb59274b895c5022741c0e3bb4949ef03881db5f42ad552f52fd634838b31593",
}

EXPECTED_FILE_PINS = {
    **STAGE_A_FROZEN_LIB_PINS,
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.lean": "ce9e1bc8924a718fd20e1578b0877f60be9c4280c2b5df8a8710cd246a68c992",
    "lake-manifest.json": "e05fab8082feabe317c593ef665972824af6a8ee0db619b35a0a57f6ef40bb67",
    "StageB.lean": "5a6dccc49c622a5bea64458e1ec31c2226fe0370cb1706f9fadeb5fe8a4eab4e",
    "Main.lean": "97a725d7b7e0d56a1d03463fee1da1b3e3e05e9c9dac3fc31a9005cf1dfafc67",
    "StageB/Q0ContextAndParallelSubst.lean": "61706fce236b9c38eed04745ad9bf2b1623fc4be45a3d0aa88940fd60213dc6d",
    "StageB/Q0TypedTransportAndPullback.lean": "be4c83d11152938650ca16eb132e4653d76dfd70dfe06a57f970a52fdc21f379",
    "StageB/Q0ConeEmptyOverlap.lean": "69deb1f7f3d223481bc89c206c0406fa8ddeb66b6e91896befe4336bbe70e270",
    "StageB/Q0Triangle2CellKernel.lean": "4aa4def7d68afb59b08a10d995a53976f38434ac6d1876cf0c07856eb46c0166",
    "StageB/Q0StageBAdversarialVectors.lean": "b192e577396da2766bb5589196431b77576f2b931b6a46ea2d3317ea127ef5b7",
}

EXPECTED_VECTOR_VERDICTS = {
    "TB-01": "verifiedExactBridge",
    "TB-02": "verifiedPathDiscrepancy",
    "TB-03": "verifiedEmptyOverlap",
    "TB-04": "rejectedIllTypedOrUnverified(illTypedBridge)",
    "TB-05": "verifiedBridgeDomainViolation",
    "TB-06": "rejectedIllTypedOrUnverified(authorityEscalation)",
}

THEOREMS_39 = [
    "lem_checkValidDomain_iff",
    "thm_rename_id",
    "thm_rename_comp",
    "thm_substParallel_id",
    "thm_substParallel_comp",
    "thm_substMap_comp",
    "thm_substMap_idCoords",
    "lem_substMap_wellScoped",
    "lem_substMap_unit",
    "lem_substMap_denote",
    "lem_substGuardMap_eval",
    "lem_substPropMap_denote",
    "lem_evalCoords_compCoords",
    "thm_unused_undefined_coord_strict_difference",
    "thm_formal_empirical_incomparable",
    "thm_authority_product_nonescalation",
    "thm_bridge_guard_proof_sound",
    "thm_transport_maps_valid_domain",
    "thm_static_domain_pullback",
    "thm_compBridge_units_preserved",
    "thm_empty_overlap_sound",
    "thm_stageB_ill_typed_universal_reject",
    "thm_stageB_authority_universal_reject",
    "thm_stageB_exact_bridge_sound",
    "thm_stageB_path_discrepancy_sound_and_exclusive",
    "thm_stageB_empty_overlap_sound_and_exclusive",
    "thm_stageB_domain_violation_sound_and_exclusive",
    "thm_2cell_exact_defect_sound",
    "thm_poly_vanishes_at_var_zero",
    "tb01_molar_energy_exact_bridge",
    "tb02_taylor_discrepancy_and_unbridgeable",
    "tb02_exact_defect_and_kappa_order",
    "tb02_unconstrained_bound_false_at_neg_v",
    "tb02_nonneg_subdomain_error_bound",
    "tb03_mach_empty_overlap_and_vacuous_blocked",
    "tb03_sos_nonlinear_empty_overlap",
    "tb04_energy_torque_ill_typed_all_witnesses",
    "tb05_intermediate_guard_domain_violation",
    "tb06_authority_escalation_blocked_all_witnesses",
]


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1048576), b""):
            h.update(chunk)
    return h.hexdigest()


def read_os_release() -> str:
    if os.path.isfile("/etc/os-release"):
        try:
            with open("/etc/os-release", "r", encoding="utf-8") as f:
                for line in f:
                    if line.startswith("PRETTY_NAME="):
                        return line.split("=", 1)[1].strip().strip('"')
        except OSError:
            pass
    return platform.platform()


def find_bin(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    elan_candidate = os.path.join(os.path.expanduser("~"), ".elan", "bin", name)
    if os.path.isfile(elan_candidate):
        return elan_candidate
    if os.path.isfile(elan_candidate + ".exe"):
        return elan_candidate + ".exe"
    raise FileNotFoundError(f"Required executable `{name}` not found on PATH or ~/.elan/bin")


def safe_extract_zip(zip_path: str, dest_dir: str) -> list[str]:
    dest_real = os.path.realpath(dest_dir)
    extracted = []
    with zipfile.ZipFile(zip_path, "r") as zf:
        for info in zf.infolist():
            rel_name = info.filename
            if info.is_dir():
                raise ValueError(f"Unexpected directory entry in archive: {rel_name}")
            if os.path.isabs(rel_name) or "\\" in rel_name:
                raise ValueError(f"Illegal path format in archive: {rel_name}")
            parts = rel_name.split("/")
            if any(p in ("", ".", "..") for p in parts):
                raise ValueError(f"Path traversal attempt in archive: {rel_name}")
            unix_mode = info.external_attr >> 16
            if (unix_mode & 0o170000) == 0o120000:
                raise ValueError(f"Symlink entry forbidden in archive: {rel_name}")

            target_path = os.path.realpath(os.path.join(dest_real, *parts))
            if os.path.commonpath([dest_real, target_path]) != dest_real:
                raise ValueError(f"Zip-Slip path escape blocked: {rel_name}")

            os.makedirs(os.path.dirname(target_path), exist_ok=True)
            with zf.open(info, "r") as src, open(target_path, "wb") as dst:
                shutil.copyfileobj(src, dst)
            extracted.append(rel_name)
    return sorted(extracted)


def verify_structured_vectors(stdout_text: str) -> tuple[bool, list[str]]:
    errors = []
    for vec_id, exp_verdict in EXPECTED_VECTOR_VERDICTS.items():
        pat = re.compile(
            rf"^VECTOR\|ID={re.escape(vec_id)}\|EXPECTED=([^|]+)\|ACTUAL=([^|]+)\|MATCH=(true|false)\|DETAIL=(.+)$",
            re.M,
        )
        m = pat.search(stdout_text)
        if not m:
            errors.append(f"Missing structured VECTOR row for {vec_id}")
            continue
        exp_col, act_col, match_col, _ = m.groups()
        if exp_col != exp_verdict or act_col != exp_verdict or match_col != "true":
            errors.append(
                f"Vector {vec_id} mismatch: expected={exp_verdict}, got EXPECTED={exp_col}, ACTUAL={act_col}, MATCH={match_col}"
            )

    if "EXTRA|ID=TB-02-DEFECT|KAPPA_MIN_DEG_2=true|NEG_V_COUNTEREXAMPLE_PROVED=true|NONNEG_BOUND_PROVED=true" not in stdout_text:
        errors.append("Missing or failed EXTRA|ID=TB-02-DEFECT verification line")
    if "EXTRA|ID=TB-03-SOS|NONLINEAR_SQUARE_EMPTY_OVERLAP=true" not in stdout_text:
        errors.append("Missing or failed EXTRA|ID=TB-03-SOS verification line")
    if "ALL STAGE B ADVERSARIAL & 2-CELL VECTORS MATCH EXPECTED: true" not in stdout_text:
        errors.append("Missing final Stage B TRUE banner")

    return (len(errors) == 0, errors)


def verify_axiom_output(stdout_text: str) -> tuple[bool, list[str]]:
    errors = []
    for bad in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if bad in stdout_text:
            errors.append(f"Forbidden axiom token detected: {bad}")

    for thm in THEOREMS_39:
        full_name = f"GrandZero.StageB.{thm}"
        pat_some = re.compile(rf"^'{re.escape(full_name)}' depends on axioms: \[(.*?)\]", re.M | re.S)
        pat_none = re.compile(rf"^'{re.escape(full_name)}' does not depend on any axioms$", re.M)
        m_some = pat_some.search(stdout_text)
        m_none = pat_none.search(stdout_text)
        if m_none:
            continue
        if not m_some:
            errors.append(f"Missing `#print axioms` output line for {full_name}")
            continue
        axs = [a.strip() for a in m_some.group(1).replace("\n", " ").split(",") if a.strip()]
        illegal = [a for a in axs if a not in ALLOWED_AXIOMS]
        if illegal:
            errors.append(f"Unexpected axiom(s) on {full_name}: {illegal}")
    return (len(errors) == 0, errors)


def main() -> int:
    here = os.path.dirname(os.path.abspath(__file__))
    zip_path = os.path.join(here, ARCHIVE_NAME)
    receipt_path = os.path.join(here, "STAGE_B_EXTERNAL_REPLAY_RECEIPT.md")
    utc_now = datetime.datetime.now(datetime.timezone.utc).isoformat()

    gh_repo = os.environ.get("GITHUB_REPOSITORY", "LOCAL_OR_NON_GH_HOST")
    gh_run_id = os.environ.get("GITHUB_RUN_ID", "N/A")
    gh_run_num = os.environ.get("GITHUB_RUN_NUMBER", "N/A")
    gh_sha = os.environ.get("GITHUB_SHA", "N/A")
    gh_actor = os.environ.get("GITHUB_ACTOR", "N/A")
    os_pretty = read_os_release()

    if not os.path.isfile(zip_path):
        print(f"FATAL: Missing {ARCHIVE_NAME} in {here}", file=sys.stderr)
        return 2

    actual_zip_size = os.path.getsize(zip_path)
    actual_zip_sha = sha256_file(zip_path)
    if actual_zip_size != EXPECTED_ARCHIVE_SIZE or actual_zip_sha != EXPECTED_ARCHIVE_SHA256:
        with open(receipt_path, "w", encoding="utf-8") as out:
            out.write("# `GRANDZERO Ω — Stage B External Independent Replay Receipt (ABORTED)`\n\n")
            out.write("- **Verdict**: **`FAIL (ARCHIVE_HASH_OR_SIZE_MISMATCH)`**\n")
            out.write(f"- **Expected**: `{EXPECTED_ARCHIVE_SIZE}` B / `{EXPECTED_ARCHIVE_SHA256}`\n")
            out.write(f"- **Actual**: `{actual_zip_size}` B / `{actual_zip_sha}`\n")
        print("FATAL: Archive SHA-256 or byte size mismatch. Aborting before extraction.", file=sys.stderr)
        return 2

    lean_bin = find_bin("lean")
    lake_bin = find_bin("lake")

    with tempfile.TemporaryDirectory(prefix="gz_stage_b_ext_") as tmp_root:
        work_dir = os.path.join(tmp_root, "stage_b")
        os.makedirs(work_dir, exist_ok=True)

        extracted_names = safe_extract_zip(zip_path, work_dir)
        has_dot_lake_pre = os.path.exists(os.path.join(work_dir, ".lake"))
        exact_file_set = (extracted_names == sorted(EXPECTED_FILE_PINS.keys()))

        pin_rows = []
        pre_pins_ok = exact_file_set and (not has_dot_lake_pre)
        for rel, exp_sha in sorted(EXPECTED_FILE_PINS.items()):
            p = os.path.join(work_dir, *rel.split("/"))
            act_sha = sha256_file(p) if os.path.isfile(p) else "MISSING"
            ok = (act_sha == exp_sha)
            if not ok:
                pre_pins_ok = False
            pin_rows.append((rel, exp_sha, act_sha, ok))

        stage_a_lineage_ok = all(
            sha256_file(os.path.join(work_dir, *rel.split("/"))) == exp_sha
            for rel, exp_sha in STAGE_A_FROZEN_LIB_PINS.items()
        )

        if not (pre_pins_ok and stage_a_lineage_ok):
            with open(receipt_path, "w", encoding="utf-8") as out:
                out.write("# `GRANDZERO Ω — Stage B External Independent Replay Receipt (ABORTED)`\n\n")
                out.write("- **Verdict**: **`FAIL (INTERNAL_SOURCE_PIN_OR_STAGE_A_LINEAGE_MISMATCH)`**\n")
            print("FATAL: Internal file SHA-256 mismatch. Aborting before build.", file=sys.stderr)
            return 2

        lean_ver = subprocess.run([lean_bin, "--version"], cwd=work_dir, capture_output=True, text=True)
        lake_ver = subprocess.run([lake_bin, "--version"], cwd=work_dir, capture_output=True, text=True)
        exact_4331 = (
            lean_ver.returncode == 0
            and EXPECTED_LEAN_VERSION_SUBSTR in lean_ver.stdout
            and EXPECTED_LEAN_COMMIT in lean_ver.stdout
        )

        build_res = subprocess.run([lake_bin, "build"], cwd=work_dir, capture_output=True, text=True)
        clean_build_pass = (build_res.returncode == 0)

        exe_res = subprocess.run([lake_bin, "exe", "stage_b_audit"], cwd=work_dir, capture_output=True, text=True)
        vec_rows_ok, vec_errors = verify_structured_vectors(exe_res.stdout)
        audit_vectors_pass = (exe_res.returncode == 0 and vec_rows_ok)

        inspect_lean = os.path.join(tmp_root, "ext_inspect_frozen_stage_b.lean")
        with open(inspect_lean, "w", encoding="utf-8") as f:
            f.write("import StageB\n\n")
            for thm in THEOREMS_39:
                f.write(f"#check @GrandZero.StageB.{thm}\n")
                f.write(f"#print axioms GrandZero.StageB.{thm}\n")

        inspect_res = subprocess.run(
            [lake_bin, "env", "lean", inspect_lean],
            cwd=work_dir,
            capture_output=True,
            text=True,
        )
        axiom_whitelist_ok, axiom_errors = verify_axiom_output(inspect_res.stdout)
        axiom_audit_pass = (
            inspect_res.returncode == 0
            and inspect_res.stderr.strip() == ""
            and axiom_whitelist_ok
        )

        source_identity_pass = (
            sha256_file(zip_path) == EXPECTED_ARCHIVE_SHA256
            and all(
                sha256_file(os.path.join(work_dir, *rel.split("/"))) == exp_sha
                for rel, exp_sha in EXPECTED_FILE_PINS.items()
            )
        )

        external_replay_pass = (
            pre_pins_ok
            and stage_a_lineage_ok
            and exact_4331
            and clean_build_pass
            and audit_vectors_pass
            and axiom_audit_pass
            and source_identity_pass
        )

        with open(receipt_path, "w", encoding="utf-8") as out:
            out.write("# `GRANDZERO Ω — Stage B External Independent Replay Receipt`\n\n")
            out.write("## 0. Environment & Run Provenance\n")
            out.write(f"- **UTC Timestamp**: `{utc_now}`\n")
            out.write(f"- **OS Release**: `{os_pretty}`\n")
            out.write(f"- **Kernel / Platform**: `{platform.platform()}` (`{platform.machine()}`)\n")
            out.write(f"- **Python Version**: `{platform.python_version()}`\n")
            out.write(f"- **GitHub Repository / Actor**: `{gh_repo}` / `{gh_actor}`\n")
            out.write(f"- **GitHub Workflow Run ID / Number / Commit**: `{gh_run_id}` / `{gh_run_num}` / `{gh_sha}`\n")
            out.write(f"- **Lean Version**: `{lean_ver.stdout.strip()}`\n")
            out.write(f"- **Lake Version**: `{lake_ver.stdout.strip().splitlines()[0] if lake_ver.stdout.strip() else ''}`\n\n")

            out.write("## 1. Seven-Boolean Conjunction Verdict Summary\n")
            out.write(f"1. `pre_pins_ok` (ZIP `{actual_zip_size}` B + `16/16` pre-build pins + no `.lake`): **`{pre_pins_ok}`**\n")
            out.write(f"2. `stage_a_lineage_ok` (`6/6` vendored `StageA` files match Stage A Final Closure SHA-256s): **`{stage_a_lineage_ok}`**\n")
            out.write(f"3. `exact_4331` (`4.33.1` & commit `{EXPECTED_LEAN_COMMIT[:12]}`): **`{exact_4331}`**\n")
            out.write(f"4. `clean_build_pass` (`lake build` exit `{build_res.returncode}`): **`{clean_build_pass}`**\n")
            out.write(f"5. `audit_vectors_pass` (`stage_b_audit` exit `{exe_res.returncode}` + field-level `TB-01..06` & `EXTRA` rows): **`{audit_vectors_pass}`**\n")
            if vec_errors:
                out.write(f"   - Vector errors: `{vec_errors}`\n")
            out.write(f"6. `axiom_audit_pass` (`39/39` Stage B theorems, exit `{inspect_res.returncode}`, allowed axioms only): **`{axiom_audit_pass}`**\n")
            if axiom_errors:
                out.write(f"   - Axiom errors: `{axiom_errors}`\n")
            out.write(f"7. `source_identity_pass` (post-build `16/16` source + ZIP SHA-256 unchanged): **`{source_identity_pass}`**\n")
            out.write(f"- **`ExternalReplayPass` (7-Boolean Conjunction)**: **`{'PASS' if external_replay_pass else 'FAIL'}`**\n\n")

            out.write("## 2. 16/16 Internal File SHA-256 Verification Table\n\n")
            out.write("| File | Expected SHA-256 | Actual SHA-256 | Match |\n| :--- | :--- | :--- | :---: |\n")
            for rel, exp_s, act_s, ok in pin_rows:
                out.write(f"| `{rel}` | `{exp_s}` | `{act_s}` | `{ok}` |\n")

            out.write("\n## 3. Raw `lake build` Log\n```text\n")
            out.write(build_res.stdout + build_res.stderr)
            out.write("\n```\n\n## 4. Raw `lake exe stage_b_audit` Structured Output\n```text\n")
            out.write(exe_res.stdout + exe_res.stderr)
            out.write("\n```\n\n## 5. Raw `#check` & `#print axioms` Output (All 39 Frozen `GrandZero.StageB` Theorems)\n```text\n")
            out.write(inspect_res.stdout + inspect_res.stderr)
            out.write("\n```\n")

        print(f"RECEIPT_WRITTEN: {receipt_path}")
        print(f"EXTERNAL_REPLAY_PASS: {external_replay_pass}")
        return 0 if external_replay_pass else 1


if __name__ == "__main__":
    sys.exit(main())
