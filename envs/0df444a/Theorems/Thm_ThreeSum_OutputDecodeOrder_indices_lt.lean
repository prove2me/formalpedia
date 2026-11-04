-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_lt
-- name    : ThreeSum.OutputDecodeOrder.indices_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:51.307877+00:00
-- url     : https://prove2.me/theorems/3279229f-638e-4fe7-afcd-9ae8d1f021d0
-- title:
--   Output Decode Order: indices lt
-- statement:
--   The Output Decode Order construction uses the indices lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L74-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L74-L84

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

theorem ThreeSum.OutputDecodeOrder.indices_lt {m : ℕ} (hm : 0 < m) (J k : ℕ) :
    ∀ a ∈ indices m J k, a < m := by sorry
