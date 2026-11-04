-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_cleanupFlag_eq_one_iff
-- name    : ThreeSum.LightOriginalSurvivorPair.cleanupFlag_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:01.178799+00:00
-- url     : https://prove2.me/theorems/cc3291f3-130b-4c40-9835-9edfd2266181
-- title:
--   Light Original Survivor Pair: cleanup Flag eq one iff
-- statement:
--   The Light Original Survivor Pair construction uses the cleanup Flag eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L143-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L143-L151

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

theorem ThreeSum.LightOriginalSurvivorPair.cleanupFlag_eq_one_iff (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    cleanupFlag A B C keysB keysC nA nB nC = 1 ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) := by sorry
