-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_solution_iff
-- name    : ThreeSum.LightOriginalSurvivorPair.solution_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:15.69348+00:00
-- url     : https://prove2.me/theorems/2de9a7f8-d3a3-4b48-8b65-e8458818e687
-- title:
--   Light Original Survivor Pair: solution iff
-- statement:
--   The Light Original Survivor Pair construction uses the solution iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L153-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L153-L159

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

theorem ThreeSum.LightOriginalSurvivorPair.solution_iff (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i < nA, ∃ j < nB, ∃ k < nC, C k = A i+B j) ↔
      cleanupFlag A B C keysB keysC nA nB nC = 1 ∨
      ∃ i < nA, ∃ j < (indices keysB nB).length, ∃ k < (indices keysC nC).length,
        C (index keysC nC k) = A i+B (index keysB nB j) := by sorry
