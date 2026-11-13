-- Prove2me | Theorems.Thm_Thm_1_4_taggedSum_between_lower_upper
-- name    : Thm_1_4.taggedSum_between_lower_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:27:55.778061+00:00
-- url     : https://prove2.me/theorems/4e5af30e-88ac-4fd3-a2b6-9d93f940a6fa
-- title:
--   Chapter 1, thm_1_4: Thm_1_4.taggedSum_between_lower_upper
-- statement:
--   Source theorem `Thm_1_4.taggedSum_between_lower_upper` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f α ≤ taggedSum P tags f α ∧
      taggedSum P tags f α ≤ upperSum P f α := by sorry

end Thm_1_4
