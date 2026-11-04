-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_pi_total
-- name    : ThreeSum.WeightedGlobalParameters.pi_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:11.985641+00:00
-- url     : https://prove2.me/theorems/2487dbad-6bef-4dcc-847e-ce4be1f94009
-- title:
--   Weighted Global Parameters: pi total
-- statement:
--   The Weighted Global Parameters construction uses the pi total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L94-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L94-L94

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.pi_total : pi0 + pi1 + pi2 = 1 := by sorry
