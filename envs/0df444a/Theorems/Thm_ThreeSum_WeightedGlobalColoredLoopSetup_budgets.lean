-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopSetup_budgets
-- name    : ThreeSum.WeightedGlobalColoredLoopSetup.budgets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:11:37.708193+00:00
-- url     : https://prove2.me/theorems/b1374e61-f467-4e8a-a71b-123eb4d3ac26
-- title:
--   Weighted Global Colored Loop Setup: budgets
-- statement:
--   The Weighted Global Colored Loop Setup construction uses the budgets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L136-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean#L136-L154

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem ThreeSum.WeightedGlobalColoredLoopSetup.budgets (hmeta : WeightedGlobalPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : WeightedGlobalArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    let S:=setup P n free menu c A B C μ
    ∀j≤S.rounds,WeightedGlobalArenaSelectedBudgets.Budget S.maps S.threshold S.cap S.Q S.input S.arrays
      P.K S.n S.U0 S.L S.R S.O j (S.state j) := by sorry
