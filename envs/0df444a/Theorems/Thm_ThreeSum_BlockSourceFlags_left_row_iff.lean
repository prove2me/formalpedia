-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceFlags_left_row_iff
-- name    : ThreeSum.BlockSourceFlags.left_row_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:26.036244+00:00
-- url     : https://prove2.me/theorems/5b5b7bb8-3592-46b1-ad8a-a4cef57ac9a1
-- title:
--   Block Source Flags: left row iff
-- statement:
--   The Block Source Flags construction uses the left row iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L42-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceFlags.lean#L42-L67

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000

theorem ThreeSum.BlockSourceFlags.left_row_iff {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) (j : Fin J) :
    LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
      (occurrenceIndices o) (candidateIndices h) (bits S)
      (mapRow h false) (mapRow h true) (leftCount h) j.val = 1 ↔
        (row S j).card=h ∧
        HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h (o j))
          (HashFamily.hashValue (mapAt h (o j)) (LocalGraph.leftWord (row S j))) ≤ localBucketCap h := by sorry
