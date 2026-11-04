-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_gibbs_expression
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.gibbs_expression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:19:36.027147+00:00
-- url     : https://prove2.me/theorems/a7cc17cb-b48f-4ad0-ac17-9d8ddae974bb
-- title:
--   Weighted Global Count Frontend Budget: gibbs expression
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the gibbs expression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L38-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L38-L42

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedQueryBudget_gibbs_expression

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.gibbs_expression {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    queryArg1^digitCount Q 1*queryArg2^digitCount Q 2/z^queryDeficit m j=envelope m j := by sorry
