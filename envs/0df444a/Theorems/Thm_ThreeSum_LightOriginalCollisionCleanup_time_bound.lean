-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_time_bound
-- name    : ThreeSum.LightOriginalCollisionCleanup.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:21.407599+00:00
-- url     : https://prove2.me/theorems/a4ef4da7-f6ed-46b7-b3e5-e52277d838cc
-- title:
--   Light Original Collision Cleanup: time bound
-- statement:
--   The Light Original Collision Cleanup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L234-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L234-L242

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
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOriginalCollisionCleanup.time_bound (keys : ℕ → ℕ) (n scanN L : ℕ) :
    time keys n scanN L≤200*n+400+
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card*
        (scanN*(120*L+330)+300) := by sorry
