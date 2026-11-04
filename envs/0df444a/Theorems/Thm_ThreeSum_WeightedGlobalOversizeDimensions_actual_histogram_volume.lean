-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_actual_histogram_volume
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.actual_histogram_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:08:53.302924+00:00
-- url     : https://prove2.me/theorems/c9401425-9dda-4169-99a6-2cc483f65554
-- title:
--   Weighted Global Oversize Dimensions: actual histogram volume
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the actual histogram volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L155-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L155-L159

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.actual_histogram_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (inflation K m : ℝ)^(4*j)*(nativePrime K m : ℝ)^j ≤
      Real.exp (tableSlope K m (nativePrime K m))*(n : ℝ)^WeightedGlobalOversizeRates.histogramCharge K m := by sorry
