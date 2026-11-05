-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_zeta_abs
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.zeta_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:19:39.429873+00:00
-- url     : https://prove2.me/theorems/8f3b8e05-bd74-48ca-9119-2516fcfa5bb3
-- title:
--   zeta_abs
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L95-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L95-L100

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.zeta_abs {N A : ℕ} (F : TritWord N→ ℤ)
    (hF : ∀ R, |F R|≤ (A:ℤ)) (R : TritWord N) :
    |binomialZeta F R|≤ (sourceZeta N A:ℤ) := by sorry
