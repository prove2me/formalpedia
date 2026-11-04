-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_original_global_key
-- name    : ThreeSum.OutputDecodeRecords.original_global_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:38.616813+00:00
-- url     : https://prove2.me/theorems/2ec81e0d-a752-4a30-87db-3f1f4010763b
-- title:
--   Output Decode Records: original global key
-- statement:
--   The Output Decode Records construction uses the original global key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L118-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L118-L122

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.original_global_key {h J k : ℕ} (hk : k < localCount h^J) :
    (globalKeys h J).getD k 0 =
      globalKey ((globalRecords h J).getD k (outputDefault h J)) := by sorry
