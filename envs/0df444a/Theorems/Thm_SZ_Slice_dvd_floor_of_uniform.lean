-- Prove2me | Theorems.Thm_SZ_Slice_dvd_floor_of_uniform
-- name    : SZ.Slice.dvd_floor_of_uniform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:22:33.963596+00:00
-- url     : https://prove2.me/theorems/edc5c2b1-65cf-4a12-8545-657ec9f5d4a0
-- title:
--   Slice: dvd floor of uniform
-- statement:
--   **Proposition 5.4.**  For `e = m - 1` and `√m ≥ p` the greedy's streams are canonical,
--   so the reduction applies and the translate produces a `ξ > 0` with `p ∣ ⌊ξ √mⁿ⌋` for every
--   `n ≥ 1`.  With `Slice.dvd_floor_of_e_le` this covers both branches of Theorem C.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L333-L368
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L333-L368

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.dvd_floor_of_uniform (S : Slice) (he : S.e = (S.m : ℤ) - 1)
    (hpsq : (S.p : ℝ) ≤ S.sq) {j k₀ : ℤ} (hj : 1 ≤ j) (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by sorry
