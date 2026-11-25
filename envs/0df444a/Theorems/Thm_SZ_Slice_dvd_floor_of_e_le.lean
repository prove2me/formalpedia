-- Prove2me | Theorems.Thm_SZ_Slice_dvd_floor_of_e_le
-- name    : SZ.Slice.dvd_floor_of_e_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:43.738175+00:00
-- url     : https://prove2.me/theorems/c6d777c8-c0b4-474f-9da9-a7418503f326
-- title:
--   Slice: dvd floor of e le
-- statement:
--   **The free case `e ≤ m - 2`** (paper Remark 2.2): every digit is already canonical, so
--   the translate alone gives the witness.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L713-L723
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L713-L723

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}

theorem SZ.Slice.dvd_floor_of_e_le (S : Slice) (he : S.e ≤ (S.m : ℤ) - 2) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by sorry
