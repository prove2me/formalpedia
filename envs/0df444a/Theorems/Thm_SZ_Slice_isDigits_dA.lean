-- Prove2me | Theorems.Thm_SZ_Slice_isDigits_dA
-- name    : SZ.Slice.isDigits_dA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:20.573873+00:00
-- url     : https://prove2.me/theorems/26ce2ba3-5135-4acd-947a-d4c078b7cdb6
-- title:
--   Slice: is Digits d A
-- statement:
--   The Slice construction uses the is Digits d A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L446-L450
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L446-L450

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

theorem SZ.Slice.isDigits_dA {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) :
    IsDigits S.m (S.dA w₀) := by sorry
