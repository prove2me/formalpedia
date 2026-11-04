-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_alpha_formulas
-- name    : ThreeSum.WeightedGlobalParameters.alpha_formulas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:58.165694+00:00
-- url     : https://prove2.me/theorems/e31a9907-2e03-4c47-9ad8-720c18453d13
-- title:
--   Weighted Global Parameters: alpha formulas
-- statement:
--   The Weighted Global Parameters construction uses the alpha formulas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L102-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L102-L105

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.alpha_formulas :
    alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by sorry
