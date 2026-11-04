-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_hit_iff
-- name    : ThreeSum.LightOriginalCollisionCleanup.hit_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:38.750737+00:00
-- url     : https://prove2.me/theorems/66082d1e-90af-4d3f-8396-e78e4b563a76
-- title:
--   Light Original Collision Cleanup: hit iff
-- statement:
--   The cleanup flag checks precisely the original records in nonsingleton
--   buckets, with their original values, rather than representations of records.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L187-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L187-L201

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

theorem ThreeSum.LightOriginalCollisionCleanup.hit_iff {keys : ℕ → ℕ} {n scanN targetN : ℕ}
    (values scan target : ℕ → ℤ) (sign : ℤ) :
    LightDeletedTwoSum.Hit (badIndex keys n) values scan target targetN scanN (badIndices keys n).length sign ↔
      ∃ i<n, (∃ j<n, j≠i ∧ keys j=keys i) ∧ LightColoredTwoSum.Hit scan target targetN scanN (values i) sign := by sorry
