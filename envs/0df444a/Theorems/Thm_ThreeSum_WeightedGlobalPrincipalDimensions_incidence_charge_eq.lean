-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_charge_eq
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.incidence_charge_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:05.77658+00:00
-- url     : https://prove2.me/theorems/a4ea4f36-5805-4719-801d-60289df753b9
-- title:
--   Weighted Global Principal Dimensions: incidence charge eq
-- statement:
--   The Weighted Global Principal Dimensions construction uses the incidence charge eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L141-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L141-L145

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.incidence_charge_eq {m : ℕ} (hm : 0 < m) :
    1+2*incidenceSlope m/Real.log (outputSize m : ℝ)=incidenceCharge m := by sorry
