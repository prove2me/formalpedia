-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_occurrenceIndex_lt
-- name    : ThreeSum.OutputDecodeRecords.occurrenceIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:36.307416+00:00
-- url     : https://prove2.me/theorems/bf6e9731-90d4-497f-88da-d9fb3573a41f
-- title:
--   Output Decode Records: occurrence Index lt
-- statement:
--   The Output Decode Records construction uses the occurrence Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L59-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L59-L61

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.occurrenceIndex_lt {h J k j : ℕ} (hj : j < J) :
    occurrenceIndex h J k j < scheduleSize h := by sorry
