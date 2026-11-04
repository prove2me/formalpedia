-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_actual_query_volume
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.actual_query_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:09:17.617227+00:00
-- url     : https://prove2.me/theorems/ee3985e5-8629-40b1-bce8-404b3ada2f2c
-- title:
--   Weighted Global Oversize Dimensions: actual query volume
-- statement:
--   This uses the literal p/Rbar output-fiber volume. It does not replace
--   that volume by M/p when the native field is larger.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L78-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L78-L111

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.actual_query_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (WeightedGlobalBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope K m)/z^1024)*(n : ℝ)^WeightedGlobalOversizeRates.queryCharge K m := by sorry
