-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedBudgets_step_budget
-- name    : ThreeSum.WeightedGlobalArenaSelectedBudgets.step_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:42:10.15621+00:00
-- url     : https://prove2.me/theorems/e8e770ca-1316-406a-8429-a6960e3126a2
-- title:
--   Weighted Global Arena Selected Budgets: step budget
-- statement:
--   All choices in a successful actual scan preserve the three budgets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L80-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L80-L95

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


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

theorem ThreeSum.WeightedGlobalArenaSelectedBudgets.step_budget (j : ℕ) (s : State (p := p) A)
    (hex : ∃i<N, budgetGood (candidates maps τ cap U V scoreBound Q I A b e ℓ L R O catalog j s) p m F j K n U0 i)
    (hL : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hR : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hlen : s.rows.length=j) :
    Budget maps τ cap Q I A K n U0 L R O (j+1)
      (step maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j s) := by sorry
