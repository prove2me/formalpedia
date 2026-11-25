-- Prove2me | Theorems.Thm_SZ_Slice_W_mem
-- name    : SZ.Slice.W_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:02.104803+00:00
-- url     : https://prove2.me/theorems/c9cf9b23-ef2c-465e-9899-dd509c2ca1e8
-- title:
--   Slice: W mem
-- statement:
--   The greedy never leaves `[0, mU]`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L426-L436
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L426-L436

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

theorem SZ.Slice.W_mem {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    0 ≤ S.W w₀ k ∧ S.W w₀ k ≤ (S.m : ℝ) * S.U := by sorry
