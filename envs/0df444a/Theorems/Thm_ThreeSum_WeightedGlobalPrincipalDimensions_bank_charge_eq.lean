-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_bank_charge_eq
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.bank_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:19.06321+00:00
-- url     : https://prove2.me/theorems/6ae37219-2f07-44ae-8f56-be48d1f597d4
-- title:
--   Weighted Global Principal Dimensions: bank charge eq
-- statement:
--   The Weighted Global Principal Dimensions construction uses the bank charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L68-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L68-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.bank_charge_eq {m : ℕ} (hm : 0 < m) :
    2*((fixedLength m : ℝ)*Real.log 2*bankEntropy)/Real.log (outputSize m : ℝ)=bankCharge m := by sorry
