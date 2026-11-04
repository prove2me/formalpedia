-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFamilyBudget_exists_good
-- name    : ThreeSum.WeightedGlobalArenaFamilyBudget.exists_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:30:22.166606+00:00
-- url     : https://prove2.me/theorems/13bc4ae0-cf93-4ebb-9fc8-a5c60dfd230f
-- title:
--   Weighted Global Arena Family Budget: exists good
-- statement:
--   This is the complete actual controller's existential premise, derived
--   from original input vectors and the previous upper budgets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L106-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFamilyBudget.lean#L106-L123

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFamilyBudget
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
open ThreeSum ThreeSum.WeightedGlobalArenaFamilyBudget
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open LightWeightedGlobalControllerFactory TernaryOriginalRowMenu TernaryExtensionEncoding
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b K : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)

theorem ThreeSum.WeightedGlobalArenaFamilyBudget.exists_good (n U0 : ℕ) (hℓ : ℓ≠0) (hlen : rows.length<A.J) (hp : 3≤p)
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
    (hPi : (p^(2*K))^r*current maps τ cap I A row L R O Q r K≤(9*pairFactor m F K)^r*U0)
    (hB : p^r*collisions A row L r I.nB≤9^r*n^2)
    (hC : p^r*collisions A row R r I.nC≤9^r*n^2) :
    ∃i<N, budgetGood (D maps τ cap U V scoreBound Q I A r b e ℓ row L R O rows catalog) p m F r K n U0 i := by sorry
