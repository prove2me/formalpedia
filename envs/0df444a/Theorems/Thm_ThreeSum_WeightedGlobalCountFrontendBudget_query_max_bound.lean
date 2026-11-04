-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_query_max_bound
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.query_max_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:48:39.983954+00:00
-- url     : https://prove2.me/theorems/ccccca78-1a19-49fa-9896-66cd3748c1c1
-- title:
--   Weighted Global Count Frontend Budget: query max bound
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the query max bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L143-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L143-L148

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedPreparedBudget_query_max_bound

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.query_max_bound {m j : ℕ} (f g : Config) (hT : f.T=bankCut m j) :
    (queryMax m j f g : ℝ)≤100000*(width (fixedLength (j*m)) f g : ℝ)^3*envelope m j := by sorry
