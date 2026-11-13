-- Prove2me | Theorems.Thm_Thm_1_4_partition_integral_between_lower_upper_id
-- name    : Thm_1_4.partition_integral_between_lower_upper_id
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:29:33.245647+00:00
-- url     : https://prove2.me/theorems/51c37e73-ae6c-4be3-b3e7-d667cb870462
-- title:
--   Chapter 1, thm_1_4: Thm_1_4.partition_integral_between_lower_upper_id
-- statement:
--   Source theorem `Thm_1_4.partition_integral_between_lower_upper_id` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F003
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem partition_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    lowerSum P g (fun x => x) ≤ ∫ x in a..b, g x ∧
      ∫ x in a..b, g x ≤ upperSum P g (fun x => x) := by sorry

end Thm_1_4
