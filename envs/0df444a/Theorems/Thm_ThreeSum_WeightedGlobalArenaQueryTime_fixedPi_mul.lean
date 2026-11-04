-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTime_fixedPi_mul
-- name    : ThreeSum.WeightedGlobalArenaQueryTime.fixedPi_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:51:38.412027+00:00
-- url     : https://prove2.me/theorems/d1f59d40-8487-4181-a43a-e0a9bca4960b
-- title:
--   Weighted Global Arena Query Time: fixed Pi mul
-- statement:
--   The Weighted Global Arena Query Time construction uses the fixed Pi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean#L29-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean#L29-L31

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTime
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup LightWeightedNearPair WeightedGlobalCountFrontendBudget
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalArenaQueryTime.fixedPi_mul (m r : ℕ) : fixedPi (r*m)=(fun d => r*fixedPi m d) := by sorry
