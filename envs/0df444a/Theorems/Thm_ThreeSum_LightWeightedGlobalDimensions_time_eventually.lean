-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_time_eventually
-- name    : ThreeSum.LightWeightedGlobalDimensions.time_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:52:30.100742+00:00
-- url     : https://prove2.me/theorems/7f2dc558-2022-44cc-abee-03bead382afe
-- title:
--   Light Weighted Global Dimensions: time eventually
-- statement:
--   Runtime computation of every size parameter costs at most n^ε eventually.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsTime.lean#L31-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsTime.lean#L31-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open WeightedGlobalSignedPadding TernaryExtensionEncoding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.LightWeightedGlobalDimensions.time_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop, (time (outputSize m) b p K n (U n) : ℝ) ≤ (n : ℝ)^ε := by sorry
