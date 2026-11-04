-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFinalPreparation_time_eq
-- name    : ThreeSum.LightTernaryFinalPreparation.time_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:39.750477+00:00
-- url     : https://prove2.me/theorems/bf459079-e3a8-4f74-952a-062f9bd42929
-- title:
--   Light Ternary Final Preparation: time eq
-- statement:
--   The Light Ternary Final Preparation construction uses the time eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFinalPreparation.lean#L83-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFinalPreparation.lean#L83-L87

import Definitions.Def_Submission_ThreeSum_LightOriginalCollisionScore
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_time_eq

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000
variable {lim : Limits}

theorem ThreeSum.LightTernaryFinalPreparation.time_eq (nB nC q W : ℕ) : time nB nC q W = 74*(nB+nC)+26*q+17*W+659 := by sorry
