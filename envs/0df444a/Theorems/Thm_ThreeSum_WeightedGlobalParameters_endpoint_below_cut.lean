-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_endpoint_below_cut
-- name    : ThreeSum.WeightedGlobalParameters.endpoint_below_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:56.036262+00:00
-- url     : https://prove2.me/theorems/1be7dfcd-2ed3-4b4c-a12b-16c8c21155b2
-- title:
--   Weighted Global Parameters: endpoint below cut
-- statement:
--   The Weighted Global Parameters construction uses the endpoint below cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L109-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L109-L109

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.endpoint_below_cut : mean/2<mean-deficit := by sorry
