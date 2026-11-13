-- Prove2me | Theorems.Thm_Thm_1_4_partition_length_sum
-- name    : Thm_1_4.partition_length_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:27:39.875443+00:00
-- url     : https://prove2.me/theorems/55381683-8a30-4b6b-9619-b090a5909554
-- title:
--   Chapter 1, thm_1_4: Thm_1_4.partition_length_sum
-- statement:
--   Source theorem `Thm_1_4.partition_length_sum` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem partition_length_sum {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, (P.pts i.succ - P.pts i.castSucc)) = b - a := by sorry

end Thm_1_4
