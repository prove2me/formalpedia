-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_polyNeed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:19:31.595539+00:00
-- url     : https://prove2.me/theorems/c0bd89f6-d17f-4c22-908b-265fef60cea2
-- title:
--   polyNeed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L315-L350
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrontendResources.lean#L315-L350

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.polyNeed {N nb groups count R : ℕ→ ℕ} {A priorCells hostWord : ℕ→ ℕ→ ℕ}
    {B : ℕ→ ℕ} {a : ℝ} (hB : PowerBound B a) (H : ℕ)
    (hN : ∀ n, N n≤ B n) (hnb : ∀ n, nb n≤ B n)
    (hgroups : ∀ n, groups n≤ B n) (hcount : ∀ n, count n≤ B n)
    (hR : ∀ n, R n≤ B n) (hfour : ∀ n, 4^(N n)≤ B n)
    (hA : ∀ n U, A n U≤ B n*(U+1)^H)
    (hprior : ∀ n U, priorCells n U≤ B n*(U+1)^H)
    (hhost : ∀ n U, hostWord n U≤ B n*(U+1)^H) :
    Light.PolyNeed (fun n U=>need (N n) (nb n) (groups n) (count n) (R n)
      (A n U) (priorCells n U) (hostWord n U)) := by sorry
