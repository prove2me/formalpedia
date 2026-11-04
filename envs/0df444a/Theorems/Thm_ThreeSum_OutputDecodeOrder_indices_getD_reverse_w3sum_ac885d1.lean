-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_reverse_w3sum_ac885d1
-- name    : ThreeSum.OutputDecodeOrder.indices_getD_reverse_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:14.180141+00:00
-- url     : https://prove2.me/theorems/807ef02a-a230-43f8-baed-4a36f414779b
-- title:
--   Output Decode Order: indices get D reverse
-- statement:
--   The Output Decode Order construction uses the indices get D reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L91-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L91-L107

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

theorem ThreeSum.OutputDecodeOrder.indices_getD_reverse_w3sum_ac885d1 (m J k : ℕ) {j : ℕ} (hj : j < J) :
    (indices m J k).getD (J-1-j) 0 = (k/m^j)%m := by sorry
