-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_right_row_iff
-- name    : ThreeSum.BlockSourceFlags.right_row_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:51.829463+00:00
-- url     : https://prove2.me/theorems/1b39536d-fa25-4c66-9d40-0df59558d110
-- title:
--   Block Source Flags: right row iff
-- statement:
--   The Block Source Flags construction uses the right row iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L69-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L69-L94

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.right_row_iff {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) (j : Fin J) :
    LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
      (occurrenceIndices o) (candidateIndices h) (bits S)
      (mapRow h true) (mapRow h false) (rightCount h) j.val = 1 ↔
        (row S j).card=h ∧
        HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h (o j))
          (HashFamily.hashValue (mapAt h (o j)) (LocalGraph.rightWord (row S j))) ≤ localBucketCap h := by sorry
