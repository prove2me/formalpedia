-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_getD_flatMap_uniform
-- name    : ThreeSum.OutputDecodeOrder.getD_flatMap_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:12:22.221343+00:00
-- url     : https://prove2.me/theorems/e8863a2f-4f7e-4f81-b36c-30ab53707671
-- title:
--   Output Decode Order: get D flat Map uniform
-- statement:
--   The Output Decode Order construction uses the get D flat Map uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L22-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L22-L43

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOrder
open RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
variable {α β : Type*}

theorem ThreeSum.OutputDecodeOrder.getD_flatMap_uniform (xs : List α) (f : α → List β) (q : ℕ)
    (hf : ∀ x ∈ xs, (f x).length=q) (da : α) (db : β)
    {z r : ℕ} (hz : z < xs.length) (hr : r < q) :
    (xs.flatMap f).getD (z*q+r) db = (f (xs.getD z da)).getD r db := by sorry
