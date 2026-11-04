-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_stage_time_bound
-- name    : ThreeSum.LightOriginalSurvivorPair.stage_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:05.078488+00:00
-- url     : https://prove2.me/theorems/6104db74-fd49-4ef3-9933-5dfbecacab4d
-- title:
--   Light Original Survivor Pair: stage time bound
-- statement:
--   The Light Original Survivor Pair construction uses the stage time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L161-L168
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L161-L168

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}

theorem ThreeSum.LightOriginalSurvivorPair.stage_time_bound (keys : ℕ → ℕ) (n scanN L : ℕ) :
    LightOriginalSurvivorStage.time keys n scanN L ≤ 280*n+720+
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card*
        (scanN*(120*L+330)+300) := by sorry
