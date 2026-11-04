-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_incidence_charge_eq
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.incidence_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:13:18.534767+00:00
-- url     : https://prove2.me/theorems/54620f6c-97a5-416c-9c4d-d563ae505aaa
-- title:
--   Weighted Global Oversize Dimensions: incidence charge eq
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the incidence charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L164-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L164-L171

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_charge_eq

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.incidence_charge_eq {K m : ℕ} (hm : 0 < m) :
    1+2*incidenceSlope K m/Real.log (outputSize m : ℝ)=WeightedGlobalOversizeRates.incidenceCharge K m := by sorry
