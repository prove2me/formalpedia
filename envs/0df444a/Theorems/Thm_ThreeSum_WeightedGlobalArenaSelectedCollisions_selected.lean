-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_selected
-- name    : ThreeSum.WeightedGlobalArenaSelectedCollisions.selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:14:42.564093+00:00
-- url     : https://prove2.me/theorems/887064e3-1f45-4013-acec-4b65024ba6fc
-- title:
--   Weighted Global Arena Selected Collisions: selected
-- statement:
--   The collision budgets of the selected original row state are exactly
--   the two actual packed-key scores consumed by cleanup.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean#L28-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean#L28-L43

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedCollisions
open WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalPairedCollisionRate
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaSelectedCollisions.selected {K m n F : ℕ} (maps : Fin F→Weight m (nativePrime K m)) (τ cap : ℕ)
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
