-- Prove2me | Theorems.Thm_Thm_1_4_rsUpperLowerCommonLimit_intervalIntegral_id
-- name    : Thm_1_4.rsUpperLowerCommonLimit_intervalIntegral_id
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:30:10.130233+00:00
-- url     : https://prove2.me/theorems/b2d8769e-19af-496f-83b6-a7354e73daff
-- title:
--   Chapter 1, thm_1_4: Thm_1_4.rsUpperLowerCommonLimit_intervalIntegral_id
-- statement:
--   Source theorem `Thm_1_4.rsUpperLowerCommonLimit_intervalIntegral_id` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem rsUpperLowerCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsUpperLowerCommonLimit a b g (fun x => x) (∫ x in a..b, g x) := by sorry

end Thm_1_4
