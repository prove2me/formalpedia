-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_original_occurrence_index
-- name    : ThreeSum.OutputDecodeRecords.original_occurrence_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:23.446406+00:00
-- url     : https://prove2.me/theorems/a5b57f92-ae34-4f9a-8ea8-a6bddb87d318
-- title:
--   Output Decode Records: original occurrence index
-- statement:
--   The Output Decode Records construction uses the original occurrence index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L100-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L100-L103

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.original_occurrence_index {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    (((globalRecords h J).getD k (outputDefault h J)) j).1.val = occurrenceIndex h J k j.val := by sorry
