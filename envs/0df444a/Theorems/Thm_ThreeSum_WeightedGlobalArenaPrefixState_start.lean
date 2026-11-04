-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_start
-- name    : ThreeSum.WeightedGlobalArenaPrefixState.start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:40:27.665142+00:00
-- url     : https://prove2.me/theorems/6c58356b-045b-4b4f-93e0-7a2f1892e6d3
-- title:
--   Weighted Global Arena Prefix State: start
-- statement:
--   The Weighted Global Arena Prefix State construction uses the start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L114-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L114-L136

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

theorem ThreeSum.WeightedGlobalArenaPrefixState.start (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ) (initial μ : ℕ→ℤ)
    (hkeep : Kept initial μ I.free)
    (hB : ∀i<I.nB,μ (addr I.free I.capacity 4+i)=0)
    (hC : ∀i<I.nC,μ (addr I.free I.capacity 5+i)=0)
    (hO : ∀i<I.requesterCount,μ (addr I.free I.capacity 6+i)=0)
    (hSpan : ∀i<A.J,μ (addr I.free I.capacity 7+i)=0) :
    Memory I A L R O 0 (WeightedGlobalArenaSelectedBudgets.initial (p := p) A) (fun _ _ => 0) initial μ := by sorry
