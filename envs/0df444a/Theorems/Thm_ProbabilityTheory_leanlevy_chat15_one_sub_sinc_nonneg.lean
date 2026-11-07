-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_one_sub_sinc_nonneg
-- name    : ProbabilityTheory.leanlevy_chat15_one_sub_sinc_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:26:24.108596+00:00
-- url     : https://prove2.me/theorems/1f2221bb-d193-4586-8126-b6859bb4a442
-- title:
--   Nonnegativity of one minus sinc
-- statement:
--   The real sinc function never exceeds one, and hence the damping factor one minus sinc is nonnegative.
-- source:
--   Pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc, Real.sinc_le_one; used in slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4 uniqueness sinc integrability proof.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_one_sub_sinc_nonneg (x : ℝ) : 0 ≤ 1 - Real.sinc x := by sorry
