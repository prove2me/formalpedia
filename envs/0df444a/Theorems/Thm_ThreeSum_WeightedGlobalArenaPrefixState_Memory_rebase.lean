-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_Memory_rebase
-- name    : ThreeSum.WeightedGlobalArenaPrefixState.Memory.rebase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:38:58.675942+00:00
-- url     : https://prove2.me/theorems/bed31605-2c99-4bb8-ad7f-980c76d815d2
-- title:
--   Memory: rebase
-- statement:
--   The invariant may refer back to the original preprocessing memory,
--   through actual arena and control initialization that preserves this prefix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L276-L280
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L276-L280

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

theorem ThreeSum.WeightedGlobalArenaPrefixState.Memory.rebase {I : Input} {A : Inputs} {L R O : ℕ→Fin (A.J+2)→ℤ}
    {j : ℕ} {s : State (p := p) A} {catalog : ℕ→ℕ→ℕ} {initial initial' μ : ℕ→ℤ}
    (H : Memory I A L R O j s catalog initial μ) (hk : Kept initial' initial I.free) :
    Memory I A L R O j s catalog initial' μ := by sorry
