-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_alpha_ordered
-- name    : ThreeSum.WeightedGlobalParameters.alpha_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:53.021735+00:00
-- url     : https://prove2.me/theorems/b213ca24-697b-4f78-8120-e3e2e124b772
-- title:
--   Weighted Global Parameters: alpha ordered
-- statement:
--   The Weighted Global Parameters construction uses the alpha ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L98-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L98-L99

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.alpha_ordered : alpha2 ≤ alpha1 ∧ alpha1 ≤ alpha0 := by sorry
