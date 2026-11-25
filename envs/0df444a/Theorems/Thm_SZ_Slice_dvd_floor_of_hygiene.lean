-- Prove2me | Theorems.Thm_SZ_Slice_dvd_floor_of_hygiene
-- name    : SZ.Slice.dvd_floor_of_hygiene
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:28.664079+00:00
-- url     : https://prove2.me/theorems/32cd4149-20a3-429f-8666-acd0e1ad2152
-- title:
--   Slice: dvd floor of hygiene
-- statement:
--   **The reduction.**  If the translate `σ` lies in the window and the greedy's streams
--   satisfy the tail hygiene \eqref{eq:L1}, then `ξ = (p j + ⟨a⟩)/m` is a positive real with
--   `p ∣ ⌊ξ √mⁿ⌋` for every `n ≥ 1`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L636-L709
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L636-L709

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

theorem SZ.Slice.dvd_floor_of_hygiene (S : Slice) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U)
    (hA : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.dA (S.w0 j k₀) i ≤ (S.m : ℤ) - 2)
    (hB : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.e - S.dB (S.w0 j k₀) i ≤ (S.m : ℤ) - 2) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by sorry
