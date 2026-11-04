-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_surviving_keys_injective
-- name    : ThreeSum.LightOriginalCollisionCleanup.surviving_keys_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:24.036835+00:00
-- url     : https://prove2.me/theorems/43813884-921d-4596-86a4-b8c2a6325dfc
-- title:
--   Light Original Collision Cleanup: surviving keys injective
-- statement:
--   The Light Original Collision Cleanup construction uses the surviving keys injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L176-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L176-L183

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

theorem ThreeSum.LightOriginalCollisionCleanup.surviving_keys_injective {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i∈good keys (counts keys n) n) (hj : j∈good keys (counts keys n) n)
    (he : keys i=keys j) : i=j := by sorry
