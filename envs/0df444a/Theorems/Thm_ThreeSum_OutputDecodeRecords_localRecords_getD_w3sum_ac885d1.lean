-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_localRecords_getD_w3sum_ac885d1
-- name    : ThreeSum.OutputDecodeRecords.localRecords_getD_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:44.325194+00:00
-- url     : https://prove2.me/theorems/9ef630af-c3c1-46c1-a0b9-4f3cac772ea3
-- title:
--   Output Decode Records: local Records get D
-- statement:
--   The Output Decode Records construction uses the local Records get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L29-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OutputDecodeRecords.lean#L29-L50

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.OutputDecodeRecords.localRecords_getD_w3sum_ac885d1 {h i : ℕ} (hi : i < localCount h) :
    (localRecords h).getD i (blockDefault h) =
      (⟨i/layerCount h,(Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr hi⟩,
        layerRecord h ⟨i%layerCount h,Nat.mod_lt _ (layerCount_pos h)⟩) := by sorry
