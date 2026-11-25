-- Prove2me | Theorems.Thm_SZ_Slice_mem_MahlerZ_of_hygiene
-- name    : SZ.Slice.mem_MahlerZ_of_hygiene
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:00.649085+00:00
-- url     : https://prove2.me/theorems/8c28a64b-f781-4136-a6c1-47e360ab16db
-- title:
--   Slice: mem Mahler Z of hygiene
-- statement:
--   **The reduction at `p = 2`** (paper Proposition 3.2): with tail hygiene the greedy's
--   streams give `√m ∈ 𝒵`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L739-L744
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L739-L744

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

theorem SZ.Slice.mem_MahlerZ_of_hygiene (S : Slice) (hp : S.p = 2) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U)
    (hA : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.dA (S.w0 j k₀) i ≤ (S.m : ℤ) - 2)
    (hB : ∀ N : ℕ, ∃ i, N ≤ i ∧ S.e - S.dB (S.w0 j k₀) i ≤ (S.m : ℤ) - 2) :
    Real.sqrt S.m ∈ MahlerZ := by sorry
