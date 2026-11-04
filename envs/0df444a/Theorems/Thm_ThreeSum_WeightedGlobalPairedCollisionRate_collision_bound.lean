-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedCollisionRate_collision_bound
-- name    : ThreeSum.WeightedGlobalPairedCollisionRate.collision_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:41:21.062237+00:00
-- url     : https://prove2.me/theorems/79e070b8-3f0d-4a22-800d-76ac2f050b4e
-- title:
--   Weighted Global Paired Collision Rate: collision bound
-- statement:
--   Exact ordered collision recurrence, evaluated at the full original
--   radix depth. The finite selector's paid factor nine is included.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L59-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedCollisionRate.lean#L59-L99

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalPairedCollisionRate.collision_bound {K m n : ℕ} (hm : 0<m) (hn : 1<n)
    (hp9 : 9<nativePrime K m) (score : ℕ→ℕ)
    (hstep : ∀ j, nativePrime K m*score (j+1)≤9*score j)
    (hinit : score 0≤n^2) :
    (score (radixLength m n) : ℝ)≤(n : ℝ)^charge K m := by sorry
