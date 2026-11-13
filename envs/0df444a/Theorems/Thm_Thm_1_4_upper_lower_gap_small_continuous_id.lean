-- Prove2me | Theorems.Thm_Thm_1_4_upper_lower_gap_small_continuous_id
-- name    : Thm_1_4.upper_lower_gap_small_continuous_id
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:29:54.182263+00:00
-- url     : https://prove2.me/theorems/ddb3a233-5239-4f80-a5a2-cc1b9cfe25f2
-- title:
--   Chapter 1, thm_1_4: Thm_1_4.upper_lower_gap_small_continuous_id
-- statement:
--   Source theorem `Thm_1_4.upper_lower_gap_small_continuous_id` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem upper_lower_gap_small_continuous_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    ClosedIntervalDarbouxGapSmall a b g (fun x => x) := by sorry

end Thm_1_4
