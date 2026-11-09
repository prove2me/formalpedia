-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat23_intInt_linear
-- name    : ProbabilityTheory.leanlevy_chat23_intInt_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:39:07.212303+00:00
-- url     : https://prove2.me/theorems/c3931cf6-aaf0-4294-82fa-cf014535b2af
-- title:
--   Symmetric interval integral of the shifted linear function
-- statement:
--   Symmetric interval integral of the shifted linear function on the interval from negative one to one.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LevyKhintchineUniqueness.lean private lemma intInt_linear near line 142

import Mathlib

open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat23_intInt_linear (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by sorry
