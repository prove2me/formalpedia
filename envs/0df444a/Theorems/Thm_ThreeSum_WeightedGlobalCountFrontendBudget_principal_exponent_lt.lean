-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_principal_exponent_lt
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.principal_exponent_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:19.8434+00:00
-- url     : https://prove2.me/theorems/296a07fc-3bf6-4e49-91be-dbb9ec245669
-- title:
--   Weighted Global Count Frontend Budget: principal exponent lt
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the principal exponent lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L387-L403
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L387-L403

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType WeightedGlobalBank WeightedGlobalParameters WeightedGlobalDimensionBounds
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverCapParameters
open WeightedGlobalOversizeOverhead WeightedGlobalOversizeDimensions WeightedGlobalPrincipalDimensions
open LightWeightedNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

theorem ThreeSum.WeightedGlobalCountFrontendBudget.principal_exponent_lt {K m : ℕ} (hK : 100000000000000000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    principalExponent K (selectedMoment K) c d m<frontendExponent := by sorry
