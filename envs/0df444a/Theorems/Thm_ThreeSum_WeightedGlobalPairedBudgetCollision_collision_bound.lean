-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedBudgetCollision_collision_bound
-- name    : ThreeSum.WeightedGlobalPairedBudgetCollision.collision_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:22:09.965537+00:00
-- url     : https://prove2.me/theorems/81dd2198-2b69-4410-b3a3-321a6ef38d7d
-- title:
--   Weighted Global Paired Budget Collision: collision bound
-- statement:
--   The Weighted Global Paired Budget Collision construction uses the collision bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedBudgetCollision.lean#L15-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedBudgetCollision.lean#L15-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
import Definitions.Def_Submission_Weighted_Global_TernaryPairedBudgetCollision
import Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_collision_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedBudgetCollision
open Real WeightedGlobalPairedCollisionRate WeightedGlobalOversizePrime WeightedGlobalCoverScale WeightedGlobalLocalParameters

theorem ThreeSum.WeightedGlobalPairedBudgetCollision.collision_bound {K m n value : ℕ} (hm : 0<m) (hn : 1<n)
    (hp9 : 9<nativePrime K m)
    (hbudget : nativePrime K m^(radixLength m n)*value≤9^(radixLength m n)*n^2) :
    (value : ℝ)≤(n : ℝ)^charge K m := by sorry
