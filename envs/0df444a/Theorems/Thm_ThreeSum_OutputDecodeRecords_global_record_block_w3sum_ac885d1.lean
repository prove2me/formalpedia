-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_global_record_block_w3sum_ac885d1
-- name    : ThreeSum.OutputDecodeRecords.global_record_block_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:05.597205+00:00
-- url     : https://prove2.me/theorems/ea5e82c8-4906-4998-b471-ef4afe853a17
-- title:
--   Output Decode Records: global record block
-- statement:
--   The Output Decode Records construction uses the global record block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L82-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L82-L98

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.global_record_block_w3sum_ac885d1 {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    ((globalRecords h J).getD k (outputDefault h J)) j =
      (localRecords h).getD (localIndex h J k j.val) (blockDefault h) := by sorry
