-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_actual_table_volume
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.actual_table_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:08:35.044761+00:00
-- url     : https://prove2.me/theorems/1baf798d-cac6-42ff-ae22-3157fc5b1c97
-- title:
--   Weighted Global Oversize Dimensions: actual table volume
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the actual table volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L115-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L115-L130

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.actual_table_volume {K m n j t : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (ht : 0 < t) :
    (inflation K m : ℝ)^(4*j)*(t : ℝ)^j ≤ Real.exp (tableSlope K m t)*
      (n : ℝ)^(2*tableSlope K m t/Real.log (outputSize m : ℝ)) := by sorry
