-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedBudgets_run_budget
-- name    : ThreeSum.WeightedGlobalArenaSelectedBudgets.run_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:43:10.520602+00:00
-- url     : https://prove2.me/theorems/e7df7cbe-1b76-41d0-8143-1f2047bcd3ce
-- title:
--   Weighted Global Arena Selected Budgets: run budget
-- statement:
--   The complete deterministic prefix induction. Every selected ordinal is
--   exactly the real three-score scan result. There are no contraction or score
--   correctness assumptions in the induction hypotheses.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L124-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedBudgets.lean#L124-L153

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInitial
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

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

theorem ThreeSum.WeightedGlobalArenaSelectedBudgets.run_budget (stop : ℕ) (hstop : stop≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hLn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hRn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hOn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hU : I.requesterCount*n^(2*K)*(A.J+2)^(2*K)*((2*K).factorial*b^(2*K))^2≤U0) :
    ∀j≤stop, Budget maps τ cap Q I A K n U0 L R O j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalog j) := by sorry
