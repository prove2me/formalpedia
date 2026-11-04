-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_endpoint_charge_eq
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.endpoint_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:55.806492+00:00
-- url     : https://prove2.me/theorems/59605245-6be6-4a75-867b-a2ea8e9f47b5
-- title:
--   Weighted Global Oversize Dimensions: endpoint charge eq
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the endpoint charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L132-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L132-L138

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_endpoint_charge_eq

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.endpoint_charge_eq {K m : ℕ} (hm : 0 < m) :
    2*tableSlope K m (endpointSize m)/Real.log (outputSize m : ℝ)=WeightedGlobalOversizeRates.endpointCharge K m := by sorry
