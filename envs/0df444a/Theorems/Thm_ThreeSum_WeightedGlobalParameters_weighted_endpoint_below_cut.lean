-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_weighted_endpoint_below_cut
-- name    : ThreeSum.WeightedGlobalParameters.weighted_endpoint_below_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:23.27292+00:00
-- url     : https://prove2.me/theorems/480e4738-4e59-48f0-af95-2fbecce15b0c
-- title:
--   Weighted Global Parameters: weighted endpoint below cut
-- statement:
--   The Weighted Global Parameters construction uses the weighted endpoint below cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L110-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L110-L111

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.weighted_endpoint_below_cut : 1025*(alpha1+2*alpha2)<2*cutSlope := by sorry
