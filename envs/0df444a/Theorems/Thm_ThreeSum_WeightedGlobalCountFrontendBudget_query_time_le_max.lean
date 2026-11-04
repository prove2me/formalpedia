-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_query_time_le_max
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.query_time_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:58.735142+00:00
-- url     : https://prove2.me/theorems/cd3c1bad-175f-4c09-bdfe-dc02393414af
-- title:
--   Weighted Global Count Frontend Budget: query time le max
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the query time le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L138-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L138-L141

import Definitions.Def_Submission_Weighted_PreparedBudget
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Theorems.Thm_ThreeSum_WeightedPreparedBudget_query_time_le_max

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.query_time_le_max {m j : ℕ} (f g : Config) (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) : LightWeightedPreparedWanted.time f g Q≤queryMax m j f g := by sorry
