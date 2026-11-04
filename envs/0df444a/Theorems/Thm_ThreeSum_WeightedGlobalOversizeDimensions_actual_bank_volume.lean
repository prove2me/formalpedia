-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_actual_bank_volume
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.actual_bank_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:06:40.855779+00:00
-- url     : https://prove2.me/theorems/4dbf8099-fb44-4d54-ad0b-34cc1c4ddf54
-- title:
--   Weighted Global Oversize Dimensions: actual bank volume
-- statement:
--   S^4 is the nonpolynomial part of the actual native greedy family.
--   The remaining family factor, all polynomial carry choices and tau are in
--   WeightedGlobalOversizeOverhead.baseFactor.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L55-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L55-L74

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.actual_bank_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (inflation K m : ℝ)^(4*j)*(bankSize m j : ℝ) ≤
      Real.exp (bankSlope K m)*(n : ℝ)^WeightedGlobalOversizeRates.bankCharge K m := by sorry
