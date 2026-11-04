-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_query_charge_eq
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.query_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:53:55.389318+00:00
-- url     : https://prove2.me/theorems/08900c54-a641-42d8-b205-f4d995bcf215
-- title:
--   Weighted Global Principal Dimensions: query charge eq
-- statement:
--   The Weighted Global Principal Dimensions construction uses the query charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L135-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L135-L139

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.query_charge_eq {m : ℕ} (hm : 0 < m) :
    1+2*querySlope m/Real.log (outputSize m : ℝ)=queryCharge m := by sorry
