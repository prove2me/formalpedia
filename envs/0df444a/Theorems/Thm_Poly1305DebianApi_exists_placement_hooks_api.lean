-- Prove2me | Theorems.Thm_Poly1305DebianApi_exists_placement_hooks_api
-- name    : Poly1305DebianApi.exists_placement_hooks_api
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T11:25:15.547638+00:00
-- url     : https://prove2.me/theorems/b63c0e4e-1216-5f39-91bd-e9ce63a4cb2e
-- title:
--   The hypotheses of the Debian libsodium Poly1305 API contracts can all be met
-- statement:
--   For every property $R(n, bs)$ of a length and a byte string such that for each $n$ some $bs$ of length $n$ has $R(n, bs)$, there are a placement $pl$ of `Poly1305DebianCt.lib` (`libsodiumDebianOnetimeauthCtLib`: Debian's libsodium 1.0.22-2 `crypto_onetimeauth` and `crypto_verify` object code for arm64, bundle `Poly1305DebianCt_PlacedObj`) and a hook table $X$ such that $pl$ is `Placeable` and `GuardUniform`, $X$ meets `MemzeroOk` (its `sodium_memzero` hook meets `Libc.explicitBzeroSpec`), `MemsetOk` (its `memset` hook meets `VerifiedLibraries.Musl.cryptoMemsetSpec`) and `RandomOk R` (its `randombytes_buf` hook meets `randombytesSpec R`), and `Link.PlacedLib.LinkOk` holds for the library, $pl$ and $X$. These are all the hypotheses of the judgments `internalOk`, `dataOk` and `randomOk` of the bundle `Poly1305DebianApi_Spec`, so the theorems stated with them do not hold vacuously. The condition on $R$ is needed: a hook must answer every requested length, so for a property that no byte string of some length satisfies, no hook meets `randombytesSpec R`.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, non-vacuity of the hypotheses of the contracts of its crypto_onetimeauth and crypto_verify object code (bundle Poly1305DebianApi_Spec): for every property of randombytes_buf output that some bytes of each length have, some placement and hook table meet all of them

import Definitions.Def_Poly1305DebianApi_Spec

namespace Poly1305DebianApi

open Arm64 Arm64.Obj

theorem exists_placement_hooks_api (R : Nat → List (BitVec 8) → Prop)
    (hR : ∀ n, ∃ bs : List (BitVec 8), bs.length = n ∧ R n bs) :
    ∃ (pl : Placement) (externs : String → Option (State → State)),
      Poly1305DebianCt.lib.Placeable pl ∧ Poly1305DebianCt.GuardUniform pl ∧
        Poly1305Libsodium.MemzeroOk externs ∧ Poly1305DebianCt.MemsetOk externs ∧
        RandomOk R externs ∧ Link.PlacedLib.LinkOk Poly1305DebianCt.lib pl externs := by
  sorry

end Poly1305DebianApi
