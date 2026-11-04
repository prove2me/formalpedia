-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_exponent_bounds
-- name    : ThreeSum.WeightedGlobalPrefixSetupResources.exponent_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:32:00.652981+00:00
-- url     : https://prove2.me/theorems/ac356c77-66a8-4d2a-83fe-1a3a1fe420ca
-- title:
--   Weighted Global Prefix Setup Resources: exponent bounds
-- statement:
--   The Weighted Global Prefix Setup Resources construction uses the exponent bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L61-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrefixSetupResources.lean#L61-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalPrefixSetupResources.exponent_bounds (m F : ℕ) :
    0≤ exponent m F ∧
    2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)≤ exponent m F ∧
    2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)≤ exponent m F := by sorry
