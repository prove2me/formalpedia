-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalFrontendResources_polyNeed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:18:46.777275+00:00
-- url     : https://prove2.me/theorems/52f405a0-de3b-4b28-a66d-d2017a3fc672
-- title:
--   polyNeed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L321-L356
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/FrontendResources.lean#L321-L356

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_FrontendResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalFrontendResources.polyNeed {N nb groups count R : ℕ→ ℕ} {A priorCells hostWord : ℕ→ ℕ→ ℕ}
    {B : ℕ→ ℕ} {a : ℝ} (hB : PowerBound B a) (H : ℕ)
    (hN : ∀ n, N n≤ B n) (hnb : ∀ n, nb n≤ B n)
    (hgroups : ∀ n, groups n≤ B n) (hcount : ∀ n, count n≤ B n)
    (hR : ∀ n, R n≤ B n) (hfour : ∀ n, 4^(N n)≤ B n)
    (hA : ∀ n U, A n U≤ B n*(U+1)^H)
    (hprior : ∀ n U, priorCells n U≤ B n*(U+1)^H)
    (hhost : ∀ n U, hostWord n U≤ B n*(U+1)^H) :
    Light.PolyNeed (fun n U=>need (N n) (nb n) (groups n) (count n) (R n)
      (A n U) (priorCells n U) (hostWord n U)) := by sorry
