-- Prove2me | Theorems.Thm_SZ_Slice_dA_mem
-- name    : SZ.Slice.dA_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:08.241411+00:00
-- url     : https://prove2.me/theorems/0921e629-bd70-443f-a7be-4cb19a582373
-- title:
--   Slice: d A mem
-- statement:
--   The Slice construction uses the d A mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L438-L440
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L438-L440

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

theorem SZ.Slice.dA_mem {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    S.PDigit (S.dA w₀ k) := by sorry
