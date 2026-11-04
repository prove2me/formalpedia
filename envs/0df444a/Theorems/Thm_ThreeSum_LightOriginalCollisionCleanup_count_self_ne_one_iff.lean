-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_count_self_ne_one_iff
-- name    : ThreeSum.LightOriginalCollisionCleanup.count_self_ne_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:12.204736+00:00
-- url     : https://prove2.me/theorems/bf21b383-6d6b-4d90-bc31-a3f0801523bd
-- title:
--   Light Original Collision Cleanup: count self ne one iff
-- statement:
--   The Light Original Collision Cleanup construction uses the count self ne one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L31-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L31-L57

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

theorem ThreeSum.LightOriginalCollisionCleanup.count_self_ne_one_iff {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) :
    counts keys n (keys i)≠1 ↔ ∃ j<n, j≠i ∧ keys j=keys i := by sorry
