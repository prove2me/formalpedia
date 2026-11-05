-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPreparedPostSelection_args_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:11:11.311032+00:00
-- url     : https://prove2.me/theorems/6abc2cf6-f2ff-4093-be97-fe8c3cdc6ff6
-- title:
--   args_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L213-L214
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L213-L214

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_args_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPostSelection_args_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_args_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.args_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPostSelection.args_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.args_length


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : Layout) (scratch matrix : ℕ) : (args S c scratch matrix).length = 148 := by sorry

attribute [defeq] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length
