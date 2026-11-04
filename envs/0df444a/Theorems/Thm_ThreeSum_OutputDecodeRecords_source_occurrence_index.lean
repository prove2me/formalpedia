-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_source_occurrence_index
-- name    : ThreeSum.OutputDecodeRecords.source_occurrence_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:39.275442+00:00
-- url     : https://prove2.me/theorems/e1d894f2-7dd2-460e-b004-e5169f4256da
-- title:
--   Output Decode Records: source occurrence index
-- statement:
--   The Output Decode Records construction uses the source occurrence index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L111-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L111-L116

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.source_occurrence_index {h J k j : ℕ} (hk : k < localCount h^J) (hj : j < J) :
    BlockCoefficientRows.occurrenceIndices
      (BlockEncoding.outputOccurrences ((globalRecords h J).getD k (outputDefault h J))) j =
        occurrenceIndex h J k j := by sorry
