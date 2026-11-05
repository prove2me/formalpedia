-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedCollisions.selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:51.129994+00:00
-- url     : https://prove2.me/theorems/d17ddaa4-3bea-4387-9ae0-c1cf9c1825e5
-- title:
--   selected
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean#L28-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean#L28-L43

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedCollisions
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedCollisions
open WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalPairedCollisionRate
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectedCollisions.selected {K m n F : ℕ} (maps : Fin F→Weight m (nativePrime K m)) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (nA U radix U0 : ℕ)
    (s : State (p := nativePrime K m) A) (X B C : ℕ→ℤ)
    (hm : 0<m) (hn : 1<n) (hp : 9<nativePrime K m) (hrate : charge K m<(7483/10000 : ℝ))
    (hbudget : Budget maps τ cap Q (base I A.J nA) A K n U0
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) (radixLength m n) s) :
    let H := selectedHash A s (radixLength m n)
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin I.nB =>
      TernaryExtensionEncoding.coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceLeft H U radix (B i.val)))).card : ℝ)≤
      (n : ℝ)^(7483/10000 : ℝ) ∧
    ((TernaryOriginalCollisions.collisionPairs (fun i : Fin I.nC =>
      TernaryExtensionEncoding.coefficientCode (WeightedGlobalNativeRequesterCoverage.sourceRight H U radix (C i.val)))).card : ℝ)≤
      (n : ℝ)^(7483/10000 : ℝ) := by sorry
