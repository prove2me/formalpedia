-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_lt
-- name    : ThreeSum.OutputDecodeOrder.indices_getD_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:12:31.884197+00:00
-- url     : https://prove2.me/theorems/d5e17b72-8dca-491e-9713-01a4a1ffe741
-- title:
--   Output Decode Order: indices get D lt
-- statement:
--   The Output Decode Order construction uses the indices get D lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L86-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L86-L89

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

theorem ThreeSum.OutputDecodeOrder.indices_getD_lt {m J k j : ℕ} (hm : 0 < m) (hj : j < J) :
    (indices m J k).getD j 0 < m := by sorry
