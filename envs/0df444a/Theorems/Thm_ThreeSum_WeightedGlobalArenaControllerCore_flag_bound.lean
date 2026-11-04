-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaControllerCore_flag_bound
-- name    : ThreeSum.WeightedGlobalArenaControllerCore.flag_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:54:36.877771+00:00
-- url     : https://prove2.me/theorems/c0d4596e-6f6f-4e90-a0e3-31ef361c6a92
-- title:
--   Weighted Global Arena Controller Core: flag bound
-- statement:
--   The Weighted Global Arena Controller Core construction uses the flag bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L68-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L68-L70

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaControllerCore.flag_bound {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : |D.flag i| ≤ 1 := by sorry
