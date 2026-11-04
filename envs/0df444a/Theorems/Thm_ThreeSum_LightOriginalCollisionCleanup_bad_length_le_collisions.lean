-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_bad_length_le_collisions
-- name    : ThreeSum.LightOriginalCollisionCleanup.bad_length_le_collisions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:33.480636+00:00
-- url     : https://prove2.me/theorems/c570c55a-53d2-424d-83f4-38c9796bd47b
-- title:
--   Light Original Collision Cleanup: bad length le collisions
-- statement:
--   The physically emitted bad-index list is charged by the literal original
--   ordered collision score, with no maximum-bucket assumption.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L61-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L61-L89

import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionCleanup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

theorem ThreeSum.LightOriginalCollisionCleanup.bad_length_le_collisions (keys : ℕ → ℕ) (n : ℕ) :
    (badIndices keys n).length≤
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card := by sorry
