-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_gibbs_parameters
-- name    : ThreeSum.WeightedGlobalParameters.gibbs_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:54:34.702717+00:00
-- url     : https://prove2.me/theorems/1765665a-583f-480d-abac-564144b07ba5
-- title:
--   Weighted Global Parameters: gibbs parameters
-- statement:
--   The Weighted Global Parameters construction uses the gibbs parameters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L116-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L116-L117

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.gibbs_parameters : 0<y ∧ y<1 ∧ 0<z ∧ z<1 := by sorry
