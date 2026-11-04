-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixFinish_header_length
-- name    : ThreeSum.LightWeightedGlobalPrefixFinish.header_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:51:36.43066+00:00
-- url     : https://prove2.me/theorems/95187c69-87c2-44cc-86ef-4bb20d253078
-- title:
--   Light Weighted Global Prefix Finish: header length
-- statement:
--   The Light Weighted Global Prefix Finish construction uses the header length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean#L33-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean#L33-L35

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixFinish
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixFinish.header_length (C : Config) (n dB dC dP tB tC tP newSpan : ℕ) :
    (header C n dB dC dP tB tC tP newSpan).length=48 := by sorry
