-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat23_intInt_quadratic
-- name    : ProbabilityTheory.leanlevy_chat23_intInt_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:39:12.574785+00:00
-- url     : https://prove2.me/theorems/7e6d3c51-5ff1-4016-a82f-0be1b19c96fa
-- title:
--   Symmetric interval integral of the shifted quadratic function
-- statement:
--   Symmetric interval integral of the shifted quadratic function on the interval from negative one to one.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LevyKhintchineUniqueness.lean private lemma intInt_quadratic near line 148

import Mathlib

open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat23_intInt_quadratic (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by sorry
