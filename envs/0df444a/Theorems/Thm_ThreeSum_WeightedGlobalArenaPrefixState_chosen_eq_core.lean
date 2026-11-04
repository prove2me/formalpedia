-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_chosen_eq_core
-- name    : ThreeSum.WeightedGlobalArenaPrefixState.chosen_eq_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:38:38.758508+00:00
-- url     : https://prove2.me/theorems/25465961-c317-4138-a868-c1716ccfc232
-- title:
--   Weighted Global Arena Prefix State: chosen eq core
-- statement:
--   Resource caps and stored catalog values do not enter the literal flag
--   or score expressions checked by the selector.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L140-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L140-L151

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


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

theorem ThreeSum.WeightedGlobalArenaPrefixState.chosen_eq_core (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p) (τ cap U V scoreBound U' : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 j : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (s : State (p := p) A)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ) (catalogs : ℕ→ℕ→ℕ→ℕ) :
    (WeightedGlobalArenaControllerCore.family maps τ cap U' Q I A
      (fun k => data I A j b k ℓ (WeightedGlobalArenaFamilyBudget.seedAt e k) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) L R).pick
      K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (scale m j K*(9*pairFactor m F K)^(j+1)*U0)-1=
      chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s := by sorry
