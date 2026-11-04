-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_alpha_positive
-- name    : ThreeSum.WeightedGlobalParameters.alpha_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:09.485127+00:00
-- url     : https://prove2.me/theorems/5f1337ff-0d0b-40a1-9d0e-d37a9a6973e1
-- title:
--   Weighted Global Parameters: alpha positive
-- statement:
--   The Weighted Global Parameters construction uses the alpha positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L96-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L96-L97

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.alpha_positive : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by sorry
