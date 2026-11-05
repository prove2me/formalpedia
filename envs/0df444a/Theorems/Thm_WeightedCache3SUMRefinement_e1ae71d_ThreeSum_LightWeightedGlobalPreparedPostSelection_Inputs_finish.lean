-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection.Inputs.finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:57:26.001821+00:00
-- url     : https://prove2.me/theorems/10f923d0-fc5b-463f-a8b1-bb897857f206
-- title:
--   finish
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L65-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L65-L110

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection.Inputs.finish {c : Layout} {lim : Limits} {d U W : ℕ} {μ ν : ℕ → ℤ}
    {A B C : ℕ → ℤ} {keysB keysC : ℕ → ℕ}
    (S : Inputs c lim d U W μ A B C keysB keysC)
    (hpowers : Powers ν c.powers W)
    (hcB : ∀ k < c.q, ν (c.histB+k) = (LightHistogram.count keysB k c.nB : ℤ))
    (hcC : ∀ k < c.q, ν (c.histC+k) = (LightHistogram.count keysC k c.nC : ℤ))
    (hkeep : Kept μ ν c.powers) : Resources c lim d U W ν A B C keysB keysC := by sorry
