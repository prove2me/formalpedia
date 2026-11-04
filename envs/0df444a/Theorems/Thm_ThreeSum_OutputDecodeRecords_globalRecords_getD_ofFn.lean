-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_globalRecords_getD_ofFn
-- name    : ThreeSum.OutputDecodeRecords.globalRecords_getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:48.088574+00:00
-- url     : https://prove2.me/theorems/2bfe6b7c-4542-4fa2-a579-52698451140b
-- title:
--   Output Decode Records: global Records get D of Fn
-- statement:
--   The Output Decode Records construction uses the global Records get D of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L74-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L74-L80

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.globalRecords_getD_ofFn {h J k : ℕ} (hk : k < localCount h^J) :
    List.ofFn ((globalRecords h J).getD k (outputDefault h J)) =
      (tuples (localRecords h) J).getD k [] := by sorry
