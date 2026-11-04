-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_count_self_positive
-- name    : ThreeSum.LightOriginalCollisionCleanup.count_self_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:50.630119+00:00
-- url     : https://prove2.me/theorems/d4937232-6506-4609-8bba-2d021931cbc0
-- title:
--   Light Original Collision Cleanup: count self positive
-- statement:
--   The Light Original Collision Cleanup construction uses the count self positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L26-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L26-L29

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

theorem ThreeSum.LightOriginalCollisionCleanup.count_self_positive {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) : 0<counts keys n (keys i) := by sorry
