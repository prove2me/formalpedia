-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_cell_word_after_ctx
-- name    : ThreeSum.LightExtensionMenuMatrix.cell_word_after_ctx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:52.274944+00:00
-- url     : https://prove2.me/theorems/c230075a-d203-4304-9e7c-324ac9cceb1c
-- title:
--   Light Extension Menu Matrix: cell word after ctx
-- statement:
--   The Light Extension Menu Matrix construction uses the cell word after ctx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuBudget.lean#L132-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuBudget.lean#L132-L137

import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionMenuMatrix
set_option maxHeartbeats 3000000

theorem ThreeSum.LightExtensionMenuMatrix.cell_word_after_ctx (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ)
    (hsize : C.p^C.dim=q) :
    LightExtensionMultiplyCell.word C q ctx ≤ ctx+1000000*(C.dim+C.p+q+2)^4 := by sorry
