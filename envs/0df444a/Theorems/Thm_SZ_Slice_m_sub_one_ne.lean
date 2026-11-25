-- Prove2me | Theorems.Thm_SZ_Slice_m_sub_one_ne
-- name    : SZ.Slice.m_sub_one_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:56:23.521951+00:00
-- url     : https://prove2.me/theorems/16912792-b79e-4f86-beb4-8d769bbc513b
-- title:
--   Slice: m sub one ne
-- statement:
--   The Slice construction uses the m sub one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L178-L179
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L178-L179

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

theorem SZ.Slice.m_sub_one_ne : ((S.m : ℝ) - 1) ≠ 0 := by sorry
