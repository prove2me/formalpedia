-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_original_output_mask
-- name    : ThreeSum.OutputDecodeRecords.original_output_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:39.997706+00:00
-- url     : https://prove2.me/theorems/dc673daf-03b9-4f95-80e3-c272766b6c3d
-- title:
--   Output Decode Records: original output mask
-- statement:
--   The Output Decode Records construction uses the original output mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L105-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L105-L109

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.original_output_mask {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    SubsetAddress.subsetMask ((((globalRecords h J).getD k (outputDefault h J)) j).2.val) =
      LocalMaskGraph.maskAt (512*h) (2*h) (maskIndex h J k j.val) := by sorry
