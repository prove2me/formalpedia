-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_actual_incidence_volume
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.actual_incidence_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:08:27.90598+00:00
-- url     : https://prove2.me/theorems/389b0b24-a89a-4230-980f-1f049a3189ce
-- title:
--   Weighted Global Oversize Dimensions: actual incidence volume
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the actual incidence volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L173-L198
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L173-L198

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.actual_incidence_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j) ≤
      Real.exp (incidenceSlope K m)*(n : ℝ)^WeightedGlobalOversizeRates.incidenceCharge K m := by sorry
