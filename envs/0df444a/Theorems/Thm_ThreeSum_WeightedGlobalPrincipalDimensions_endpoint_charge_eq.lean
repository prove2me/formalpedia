-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_endpoint_charge_eq
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.endpoint_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:16.068916+00:00
-- url     : https://prove2.me/theorems/ca97edca-9544-4c1a-8aef-b99cbc940b33
-- title:
--   Weighted Global Principal Dimensions: endpoint charge eq
-- statement:
--   The Weighted Global Principal Dimensions construction uses the endpoint charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L73-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L73-L77

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.endpoint_charge_eq {m : ℕ} (hm : 0 < m) :
    2*Real.log (endpointSize m : ℝ)/Real.log (outputSize m : ℝ)=endpointCharge m := by sorry
