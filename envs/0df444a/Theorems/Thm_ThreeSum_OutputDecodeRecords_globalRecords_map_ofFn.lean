-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_globalRecords_map_ofFn
-- name    : ThreeSum.OutputDecodeRecords.globalRecords_map_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:03.356086+00:00
-- url     : https://prove2.me/theorems/f4edd1a1-9c89-4435-8e10-a23cbc914343
-- title:
--   Output Decode Records: global Records map of Fn
-- statement:
--   The Output Decode Records construction uses the global Records map of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L66-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L66-L68

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.globalRecords_map_ofFn (h J : ℕ) :
    (globalRecords h J).map List.ofFn = tuples (localRecords h) J := by sorry
