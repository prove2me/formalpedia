-- Prove2me | Theorems.Thm_SZ_Slice_W_ne_val
-- name    : SZ.Slice.W_ne_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:21:33.490784+00:00
-- url     : https://prove2.me/theorems/51b00566-0904-497d-ab4e-806730196141
-- title:
--   Slice: W ne val
-- statement:
--   The state is never a point of `ℤ[√m]` with small `√m`-coordinate — in particular never
--   `0` and never the trap fixed point `mU = m + m√m`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L174-L188
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L174-L188

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.W_ne_val (he : S.e = (S.m : ℤ) - 1) {j k₀ : ℤ} (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (k : ℕ) {p q : ℤ}
    (hq : q ≤ (S.m : ℤ)) : S.W (S.w0 j k₀) k ≠ (p : ℝ) + (q : ℝ) * S.sq := by sorry
