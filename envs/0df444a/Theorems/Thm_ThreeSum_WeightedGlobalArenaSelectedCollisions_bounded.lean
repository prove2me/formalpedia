-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedCollisions_bounded
-- name    : ThreeSum.WeightedGlobalArenaSelectedCollisions.bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:15:51.781756+00:00
-- url     : https://prove2.me/theorems/16061173-f2bb-4894-97c6-f6b59d6a0018
-- title:
--   Weighted Global Arena Selected Collisions: bounded
-- statement:
--   The paid collision cleanup exponent includes the actual selector's
--   factor nine, and holds for every ordered collision budget.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean#L19-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedCollisions.lean#L19-L24

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

theorem ThreeSum.WeightedGlobalArenaSelectedCollisions.bounded {K m n value : ℕ} (hm : 0<m) (hn : 1<n)
    (hp : 9<nativePrime K m) (hrate : charge K m<(7483/10000 : ℝ))
    (hbudget : (nativePrime K m)^(radixLength m n)*value≤9^(radixLength m n)*n^2) :
    (value : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by sorry
