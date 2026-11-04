-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
-- name    : ThreeSum.LightWeightedGlobalPreparedPostSelection.Inputs.finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:17:49.480568+00:00
-- url     : https://prove2.me/theorems/d730f712-3e8e-486d-978b-b1948bf2b4bf
-- title:
--   Inputs: finish
-- statement:
--   The Inputs construction uses the finish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L65-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L65-L110

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPreparedPostSelection.Inputs.finish {c : Layout} {lim : Limits} {d U W : ℕ} {μ ν : ℕ → ℤ}
    {A B C : ℕ → ℤ} {keysB keysC : ℕ → ℕ}
    (S : Inputs c lim d U W μ A B C keysB keysC)
    (hpowers : Powers ν c.powers W)
    (hcB : ∀ k < c.q, ν (c.histB+k) = (LightHistogram.count keysB k c.nB : ℤ))
    (hcC : ∀ k < c.q, ν (c.histC+k) = (LightHistogram.count keysC k c.nC : ℤ))
    (hkeep : Kept μ ν c.powers) : Resources c lim d U W ν A B C keysB keysC := by sorry
