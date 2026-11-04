-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_mem_badIndices
-- name    : ThreeSum.LightOriginalCollisionCleanup.mem_badIndices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:35.406241+00:00
-- url     : https://prove2.me/theorems/62139a08-c775-44f8-8017-104aee9f720a
-- title:
--   Light Original Collision Cleanup: mem bad Indices
-- statement:
--   The Light Original Collision Cleanup construction uses the mem bad Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L165-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L165-L174

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

theorem ThreeSum.LightOriginalCollisionCleanup.mem_badIndices {keys : ℕ → ℕ} {n i : ℕ} :
    i∈badIndices keys n ↔ i<n ∧ ∃ j<n, j≠i ∧ keys j=keys i := by sorry
