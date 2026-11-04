-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
-- name    : ThreeSum.LightOriginalCollisionCleanup.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:40:38.971586+00:00
-- url     : https://prove2.me/theorems/3a27173e-c518-46dc-a02a-ddf38b996ef6
-- title:
--   Light Original Collision Cleanup: program length
-- statement:
--   The Light Original Collision Cleanup construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L248-L248
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalCollisionCleanup.lean#L248-L248

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

theorem ThreeSum.LightOriginalCollisionCleanup.program_length : program.length=6 := by sorry

attribute [defeq] ThreeSum.LightOriginalCollisionCleanup.program_length
