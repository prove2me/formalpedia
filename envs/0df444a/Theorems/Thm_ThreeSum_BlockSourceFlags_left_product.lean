-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_left_product
-- name    : ThreeSum.BlockSourceFlags.left_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:22.851563+00:00
-- url     : https://prove2.me/theorems/cc756da8-e41c-4491-b7f7-9275d829edbc
-- title:
--   Block Source Flags: left product
-- statement:
--   The Block Source Flags construction uses the left product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L96-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L96-L108

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.left_product {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h false) (mapRow h true) (leftCount h)) J =
      if LeftAllowed o S then 1 else 0 := by sorry
