-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_time_bound
-- name    : ThreeSum.LightOriginalSurvivorPair.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:46.132626+00:00
-- url     : https://prove2.me/theorems/8c408b06-818f-4293-9b05-031ed0b71ecd
-- title:
--   Light Original Survivor Pair: time bound
-- statement:
--   The Light Original Survivor Pair construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L170-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L170-L179

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_time_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}

theorem ThreeSum.LightOriginalSurvivorPair.time_bound (keysB keysC : ℕ → ℕ) (nA nB nC L : ℕ) :
    time keysB keysC nA nB nC L ≤ 280*(nB+nC)+1640+
      ((TernaryOriginalCollisions.collisionPairs (fun i : Fin nB => keysB i.val)).card+
       (TernaryOriginalCollisions.collisionPairs (fun i : Fin nC => keysC i.val)).card)*
        (nA*(120*L+330)+300) := by sorry
