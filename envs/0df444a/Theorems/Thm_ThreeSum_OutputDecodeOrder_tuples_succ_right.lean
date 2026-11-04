-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeOrder_tuples_succ_right
-- name    : ThreeSum.OutputDecodeOrder.tuples_succ_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:11.166041+00:00
-- url     : https://prove2.me/theorems/44fcafe8-628a-41c6-bf8c-1ca8be3c670e
-- title:
--   Output Decode Order: tuples succ right
-- statement:
--   The Output Decode Order construction uses the tuples succ right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L45-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeOrder.lean#L45-L63

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

theorem ThreeSum.OutputDecodeOrder.tuples_succ_right (base : List α) (J : ℕ) :
    tuples base (J+1) = (tuples base J).flatMap fun xs => base.map fun a => xs++[a] := by sorry
