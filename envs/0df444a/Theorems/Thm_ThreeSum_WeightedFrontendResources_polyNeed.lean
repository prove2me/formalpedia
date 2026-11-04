-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrontendResources_polyNeed
-- name    : ThreeSum.WeightedFrontendResources.polyNeed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:23:40.706955+00:00
-- url     : https://prove2.me/theorems/61005d73-be2f-474b-bdda-e3e42fa0b7c8
-- title:
--   Weighted Frontend Resources: poly Need
-- statement:
--   Fixed-degree moment channels may make source magnitudes large, but only
--   polynomially in the original input magnitude. This is the compiler's actual
--   two-parameter polynomial-resource predicate.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L315-L350
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean#L315-L350

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedFrontendResources.polyNeed {N nb groups count R : ℕ→ ℕ} {A priorCells hostWord : ℕ→ ℕ→ ℕ}
    {B : ℕ→ ℕ} {a : ℝ} (hB : PowerBound B a) (H : ℕ)
    (hN : ∀ n, N n≤ B n) (hnb : ∀ n, nb n≤ B n)
    (hgroups : ∀ n, groups n≤ B n) (hcount : ∀ n, count n≤ B n)
    (hR : ∀ n, R n≤ B n) (hfour : ∀ n, 4^(N n)≤ B n)
    (hA : ∀ n U, A n U≤ B n*(U+1)^H)
    (hprior : ∀ n U, priorCells n U≤ B n*(U+1)^H)
    (hhost : ∀ n U, hostWord n U≤ B n*(U+1)^H) :
    Light.PolyNeed (fun n U=>need (N n) (nb n) (groups n) (count n) (R n)
      (A n U) (priorCells n U) (hostWord n U)) := by sorry
