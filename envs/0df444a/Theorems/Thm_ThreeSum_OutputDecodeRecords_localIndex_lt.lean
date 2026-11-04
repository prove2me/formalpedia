-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_localIndex_lt
-- name    : ThreeSum.OutputDecodeRecords.localIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:21.709814+00:00
-- url     : https://prove2.me/theorems/5928344a-0484-494d-aced-62e2235a9186
-- title:
--   Output Decode Records: local Index lt
-- statement:
--   The Output Decode Records construction uses the local Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L56-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L56-L57

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.localIndex_lt {h J k j : ℕ} (hj : j < J) : localIndex h J k j < localCount h := by sorry
