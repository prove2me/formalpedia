-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_tuples_getD_indices_w3sum_ac885d1
-- name    : ThreeSum.OutputDecodeOrder.tuples_getD_indices_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:13.298817+00:00
-- url     : https://prove2.me/theorems/eb42f153-42d7-4f80-b072-4a847972ffa8
-- title:
--   Output Decode Order: tuples get D indices
-- statement:
--   The Output Decode Order construction uses the tuples get D indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L109-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L109-L128

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

theorem ThreeSum.OutputDecodeOrder.tuples_getD_indices_w3sum_ac885d1 (base : List α) (da : α) (hm : 0 < base.length)
    (J k : ℕ) (hk : k < base.length^J) :
    (tuples base J).getD k [] = (indices base.length J k).map (fun i => base.getD i da) := by sorry
