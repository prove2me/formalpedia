-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_table_word_polynomial
-- name    : ThreeSum.LightExtensionMenuMatrix.table_word_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:26.1106+00:00
-- url     : https://prove2.me/theorems/7a21a94f-cf17-4746-ba65-89afce817d44
-- title:
--   Light Extension Menu Matrix: table word polynomial
-- statement:
--   The Light Extension Menu Matrix construction uses the table word polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuBudget.lean#L102-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuBudget.lean#L102-L124

import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionMenuMatrix
set_option maxHeartbeats 3000000

theorem ThreeSum.LightExtensionMenuMatrix.table_word_polynomial (q ctx p dim powers a b : ℕ) :
    LightExtensionMultiplyTable.word q ctx p dim powers a b ≤
      100000*(q+ctx+p+dim+powers+a+b+2)^2 := by sorry
