-- Prove2me | Theorems.Thm_Poly1305DebianCt_exists_placement_hooks
-- name    : Poly1305DebianCt.exists_placement_hooks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T15:13:31.715852+00:00
-- url     : https://prove2.me/theorems/4032eb33-81f3-5dd6-a552-b758b0c5f1f6
-- title:
--   The hypotheses of the constant-time judgments for Debian libsodium Poly1305 can all be met
-- statement:
--   There are a placement $pl$ of `Poly1305DebianCt.lib`, that is `libsodiumDebianOnetimeauthCtLib` (Debian's libsodium 1.0.22-2 `crypto_onetimeauth` and `crypto_verify` object code for arm64, bundle `Poly1305DebianCt_PlacedObj`), and a hook table $X$ such that $pl$ is `Placeable` and `GuardUniform`, $X$ meets `MemzeroOk` (its `sodium_memzero` hook meets `Libc.explicitBzeroSpec`) and `MemsetOk` (its `memset` hook meets `VerifiedLibraries.Musl.cryptoMemsetSpec`), and `Link.PlacedLib.LinkOk lib pl X` holds. These are all the hypotheses of the judgments `ctInternalOk` and `ctPublicOk` of the bundle `Poly1305DebianCt_Spec`, so the theorems stated with them do not hold vacuously.
--
--   A witness: the code at `0x100000`; the external functions at distinct addresses from `0x101000` to `0x101140`, past the code, with the GOT slot of `__stack_chk_guard` at `0x101040` among them; the data objects at `0x102000`, `0x102200`, `0x102400` and `0x102600`; no linker relaxation, so every access to `__stack_chk_guard` goes through its GOT slot. The `sodium_memzero` hook writes `x1` zero bytes at the address in `x0`, the `memset` hook writes `x2` copies of the low byte of `x1` there, and each then continues at the address in `x30`. Every other name has no hook.
--   $$\exists\, pl\ X,\ \mathrm{Placeable}(pl) \wedge \mathrm{GuardUniform}(pl) \wedge \mathrm{MemzeroOk}(X) \wedge \mathrm{MemsetOk}(X) \wedge \mathrm{LinkOk}(\mathtt{lib}, pl, X)$$
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, non-vacuity of the hypotheses of the constant-time judgments of its crypto_onetimeauth and crypto_verify object code (bundle Poly1305DebianCt_Spec): some placement and hook table meet all of them

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

open Arm64 Arm64.Obj

theorem exists_placement_hooks :
    ∃ (pl : Placement) (externs : String → Option (State → State)),
      lib.Placeable pl ∧ GuardUniform pl ∧
        Poly1305Libsodium.MemzeroOk externs ∧ MemsetOk externs ∧
        Link.PlacedLib.LinkOk lib pl externs := by
  sorry

end Poly1305DebianCt
