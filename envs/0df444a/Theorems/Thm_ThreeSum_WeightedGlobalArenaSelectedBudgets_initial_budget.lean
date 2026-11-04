-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedBudgets_initial_budget
-- name    : ThreeSum.WeightedGlobalArenaSelectedBudgets.initial_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:42:13.9062+00:00
-- url     : https://prove2.me/theorems/2fd46a77-eede-4994-81a0-c1d9120d551e
-- title:
--   Weighted Global Arena Selected Budgets: initial budget
-- statement:
--   The Weighted Global Arena Selected Budgets construction uses the initial budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L105-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L105-L119

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedBudgets
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)

theorem ThreeSum.WeightedGlobalArenaSelectedBudgets.initial_budget
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hU : I.requesterCount*n^(2*K)*(A.J+2)^(2*K)*((2*K).factorial*b^(2*K))^2≤U0) :
    Budget maps τ cap Q I A K n U0 L R O 0 (initial A) := by sorry
