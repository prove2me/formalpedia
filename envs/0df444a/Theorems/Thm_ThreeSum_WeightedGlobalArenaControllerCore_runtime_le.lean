-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaControllerCore_runtime_le
-- name    : ThreeSum.WeightedGlobalArenaControllerCore.runtime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:45:26.426199+00:00
-- url     : https://prove2.me/theorems/0ea28758-ad17-4d70-bbb3-84861bc952e7
-- title:
--   Weighted Global Arena Controller Core: runtime le
-- statement:
--   The Weighted Global Arena Controller Core construction uses the runtime le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L32-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerCore.lean#L32-L36

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

theorem ThreeSum.WeightedGlobalArenaControllerCore.runtime_le {C : Config} [Fact C.p.Prime] (D : Family C)
    (K R S n : ℕ) (raws : List ℤ) (words maps : List ℕ) (i : ℕ) (hi : i < n) :
    (D.candidate i).runtime K R S raws words maps ≤ seedTime D K R S n raws words maps := by sorry
