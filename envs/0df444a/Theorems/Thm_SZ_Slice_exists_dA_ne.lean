-- Prove2me | Theorems.Thm_SZ_Slice_exists_dA_ne
-- name    : SZ.Slice.exists_dA_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:01:11.324329+00:00
-- url     : https://prove2.me/theorems/636e9591-11b1-41c3-9691-bbdf617bdde4
-- title:
--   Slice: exists d A ne
-- statement:
--   **L1(a).**  The `a`-digits are not eventually stuck at the top digit `e`: were they,
--   the offset would be the constant `e(1+√m) = (m-1)U`, the orbit would sit at the fixed
--   point `mU = m + m√m`, and growth forbids that.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L195-L252
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L195-L252

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.exists_dA_ne (he : S.e = (S.m : ℤ) - 1) (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ}
    (hk : 1 ≤ k₀) (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (N : ℕ) :
    ∃ k, N ≤ k ∧ S.dA (S.w0 j k₀) k ≠ S.e := by sorry
