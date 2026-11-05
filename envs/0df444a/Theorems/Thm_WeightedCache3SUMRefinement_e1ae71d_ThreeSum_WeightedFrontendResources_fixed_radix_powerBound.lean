-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_fixed_radix_powerBound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.fixed_radix_powerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:21:38.034348+00:00
-- url     : https://prove2.me/theorems/05609706-3df4-42ee-8f5a-b98bf93683f1
-- title:
--   fixed_radix_powerBound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L356-L373
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L356-L373

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.fixed_radix_powerBound {m : ℕ} (hm : 0< m) (b : ℕ) :
    PowerBound (fun n=>(b+1)^radixLength m n)
      (2*Real.log (b+1:ℕ)/Real.log (outputSize m:ℝ)) := by sorry
