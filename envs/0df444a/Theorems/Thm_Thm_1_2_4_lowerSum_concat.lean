-- Prove2me | Theorems.Thm_Thm_1_2_4_lowerSum_concat
-- name    : Thm_1_2_4.lowerSum_concat
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:54:30.924687+00:00
-- url     : https://prove2.me/theorems/9c940454-1f70-4084-9220-26e2c3e6a160
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.lowerSum_concat
-- statement:
--   Source theorem `Thm_1_2_4.lowerSum_concat` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

theorem lowerSum_concat {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) (f α : ℝ → ℝ) :
    lowerSum (concatPartition P1 P2) f α = lowerSum P1 f α + lowerSum P2 f α := by sorry

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
