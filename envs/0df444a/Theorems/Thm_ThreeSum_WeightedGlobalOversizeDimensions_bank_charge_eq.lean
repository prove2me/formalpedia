-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_bank_charge_eq
-- name    : ThreeSum.WeightedGlobalOversizeDimensions.bank_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:42.386816+00:00
-- url     : https://prove2.me/theorems/b937ad81-6dc0-4c7c-9568-fad9d0b6d020
-- title:
--   Weighted Global Oversize Dimensions: bank charge eq
-- statement:
--   The Weighted Global Oversize Dimensions construction uses the bank charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L31-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryOversizeDimensions.lean#L31-L37

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_bank_charge_eq

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType

theorem ThreeSum.WeightedGlobalOversizeDimensions.bank_charge_eq {K m : ℕ} (hm : 0 < m) :
    2*bankSlope K m/Real.log (outputSize m : ℝ)=WeightedGlobalOversizeRates.bankCharge K m := by sorry
