-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_start_initialized
-- name    : ThreeSum.WeightedGlobalArenaPrefixState.start_initialized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:43:13.820418+00:00
-- url     : https://prove2.me/theorems/d5741d3b-ea8f-4cd1-968b-d2358f5da528
-- title:
--   Weighted Global Arena Prefix State: start initialized
-- statement:
--   The Weighted Global Arena Prefix State construction uses the start initialized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L182-L190
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L182-L190

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPrefixState.start_initialized (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (values : List ℤ) (initial μ : ℕ→ℤ)
    (H : LightWeightedGlobalPrefixInit.Initialized (config p 1 I A 0) (addr I.free I.capacity 3) values initial μ) :
    Memory I A L R O 0 (WeightedGlobalArenaSelectedBudgets.initial (p := p) A) (fun _ _ => 0) initial μ := by sorry
