-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_good
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget.good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:54.383183+00:00
-- url     : https://prove2.me/theorems/28810f7c-bda7-4b2d-b8ed-b11315dc49cd
-- title:
--   good
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L55-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L55-L83

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget.good (maps : Fin F→Weight m p) (τ cap tag : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (j b K n U0 : ℕ) (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (s : State (p := p) A) (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ)
    (hbudget : Budget maps τ cap Q I A K n U0 L R O j s)
    (hj : j<A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hLn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+L i t.val)
    (hRn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+R i t.val)
    (hOn : ∀ i (t : Fin (A.J+2)), 0≤(p : ℤ)+O i t.val)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E) (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E) :
    ∃i<N,LightTernaryRowSelector.Good
      (WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).flag
      (WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreB
      (WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreC
      ((WeightedGlobalArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)) i := by sorry
