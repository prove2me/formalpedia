-- Prove2me | Theorems.Thm_Thm_1_2_4_taggedCommonLimit_left
-- name    : Thm_1_2_4.taggedCommonLimit_left
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:46:22.312502+00:00
-- url     : https://prove2.me/theorems/fe272a6b-546d-4b0e-b5bf-c6a543aa32e8
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.taggedCommonLimit_left
-- statement:
--   Source theorem `Thm_1_2_4.taggedCommonLimit_left` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

theorem taggedCommonLimit_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    TaggedCommonLimit a c f α (lowerDarboux a c f α) := by sorry

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
