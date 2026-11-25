-- Prove2me | Theorems.Thm_Poly1305Debian_exists_placement_hooks
-- name    : Poly1305Debian.exists_placement_hooks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T19:56:40.520802+00:00
-- url     : https://prove2.me/theorems/3db937dd-d422-5132-88ab-8d8c1066dcda
-- title:
--   The hypotheses of the Debian libsodium Poly1305 contracts can all be met
-- statement:
--   There are a placement $pl$ of `libsodiumDebianOnetimeauthLib` (Debian's libsodium 1.0.22-2 `crypto_onetimeauth` object code for arm64, bundle `Poly1305Debian_PlacedObj`) and a hook table $X$ such that $pl$ is `Placeable` and `GuardUniform`, $X$ meets `MemzeroOk` (its `sodium_memzero` hook meets `Libc.explicitBzeroSpec`) and `MemsetOk` (its `memset` hook meets `VerifiedLibraries.Musl.cryptoMemsetSpec`), and `Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl X` holds. These are all the hypotheses of the judgments `internalOk` and `publicOk` of the bundle `Poly1305Debian_Spec`, so the theorems stated with them do not hold vacuously.
--
--   A witness: the code at `0x100000`; the external functions at distinct addresses from `0x101000` to `0x101140`, past the code; the data objects at `0x102000`, `0x102200` and `0x102400`; no linker relaxation. The `sodium_memzero` hook writes `x1` zero bytes at the address in `x0`, the `memset` hook writes `x2` copies of the low byte of `x1` there, and each then continues at the address in `x30`. Every other name has no hook.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, non-vacuity of the hypotheses of the contracts of its crypto_onetimeauth object code (bundle Poly1305Debian_Spec): some placement and hook table meet all of them

import Definitions.Def_Poly1305Debian_Spec

namespace Poly1305Debian

open Arm64 Arm64.Obj

theorem exists_placement_hooks :
    ∃ (pl : Placement) (externs : String → Option (State → State)),
      libsodiumDebianOnetimeauthLib.Placeable pl ∧ GuardUniform pl ∧
        Poly1305Libsodium.MemzeroOk externs ∧ MemsetOk externs ∧
        Link.PlacedLib.LinkOk libsodiumDebianOnetimeauthLib pl externs := by
  sorry

end Poly1305Debian
