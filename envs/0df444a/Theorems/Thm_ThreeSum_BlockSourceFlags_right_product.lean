-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_right_product
-- name    : ThreeSum.BlockSourceFlags.right_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:55.219653+00:00
-- url     : https://prove2.me/theorems/9dd83000-b184-4ec6-8c87-1de45e1fbea2
-- title:
--   Block Source Flags: right product
-- statement:
--   The Block Source Flags construction uses the right product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L110-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L110-L122

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.right_product {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h true) (mapRow h false) (rightCount h)) J =
      if RightAllowed o S then 1 else 0 := by sorry
