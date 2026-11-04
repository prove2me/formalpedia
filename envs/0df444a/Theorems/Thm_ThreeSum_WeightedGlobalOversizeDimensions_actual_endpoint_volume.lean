-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_actual_endpoint_volume
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.actual_endpoint_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:08:24.593193+00:00
-- url     : https://prove2.me/theorems/c56565ce-7312-43ac-b0d3-ffab98f4bfb1
-- title:
--   Weighted Global Oversize Dimensions: actual endpoint volume
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the actual endpoint volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L148-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L148-L153

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.actual_endpoint_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (inflation K m : ℝ)^(4*j)*(endpointSize m : ℝ)^j ≤
      Real.exp (tableSlope K m (endpointSize m))*(n : ℝ)^WeightedGlobalOversizeRates.endpointCharge K m := by sorry
