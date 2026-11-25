-- Prove2me | Theorems.Thm_SZ_Slice_dB_mem
-- name    : SZ.Slice.dB_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:17.910732+00:00
-- url     : https://prove2.me/theorems/a670f153-23f5-4ac3-94ae-61eb097321a7
-- title:
--   Slice: d B mem
-- statement:
--   The Slice construction uses the d B mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L442-L444
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L442-L444

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

theorem SZ.Slice.dB_mem {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    S.PDigit (S.dB w₀ k) := by sorry
