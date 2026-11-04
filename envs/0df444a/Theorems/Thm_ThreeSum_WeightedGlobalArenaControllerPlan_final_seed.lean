-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaControllerPlan_final_seed
-- name    : ThreeSum.WeightedGlobalArenaControllerPlan.final_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:26:44.870049+00:00
-- url     : https://prove2.me/theorems/48aa98fe-d19e-42b9-8f20-c87fc52ce772
-- title:
--   Weighted Global Arena Controller Plan: final seed
-- statement:
--   The live controller record survives the replay and span extension.
--   This supplies the literal header premise of the actual commit suffix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerPlan.lean#L113-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaControllerPlan.lean#L113-L129

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaControllerPlan
open Light LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open WeightedGlobalArenaControllerCore WeightedGlobalArenaLayout
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaControllerPlan.final_seed {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K R S i : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ→ℤ}
    (h : Final I D K R S i (addr I.free I.capacity 8) raws words maps μ ν)
    (hc : 106≤I.capacity) {xs : List ℤ} (hlen : xs.length≤I.capacity)
    (hseed : Seg μ (addr I.free I.capacity 3) xs) :
    Seg ν (addr I.free I.capacity 3) xs := by sorry
