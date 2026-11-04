-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_eq_new
-- name    : ThreeSum.WeightedGlobalCountFrontendBudget.envelope_eq_new
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:41.914197+00:00
-- url     : https://prove2.me/theorems/d09297c0-ef23-4d55-958b-64e9047a49e5
-- title:
--   Weighted Global Count Frontend Budget: envelope eq new
-- statement:
--   The Weighted Global Count Frontend Budget construction uses the envelope eq new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L25-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/CountFrontendBudget.lean#L25-L32

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

theorem ThreeSum.WeightedGlobalCountFrontendBudget.envelope_eq_new (m j : ℕ) : envelope m j=WeightedQueryBudget.envelope (j*m) := by sorry
