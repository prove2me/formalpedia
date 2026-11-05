-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaBudgetExistence_exists_seed
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaBudgetExistence.exists_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:52:17.791957+00:00
-- url     : https://prove2.me/theorems/09c95367-d64b-4dc8-8d26-7b206ca09264
-- title:
--   exists_seed
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaBudgetExistence.lean#L47-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaBudgetExistence.lean#L47-L101

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaBudgetExistence
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaBudgetExistence
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverLocal
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
open TernaryOriginalRowMenu TernaryExtensionEncoding WeightedGlobalArenaSeedData
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaBudgetExistence.exists_seed (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (A : Inputs)
    (ℓ : E→ₗ[ZMod p] ZMod p) (hℓ : ℓ≠0)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (rows : List (Fin A.J→ZMod p)) (hlen : rows.length<A.J)
    (r K b n U0 : ℕ) (hp : 3≤p)
    (hL : ∀ i (t : Fin (A.J+2)), (L i t.val).natAbs≤b)
    (hR : ∀ i (t : Fin (A.J+2)), (R i t.val).natAbs≤b)
    (hinjL : Function.Injective (fun i : Fin I.nB => fun t : Fin (A.J+2) => (L i.val t.val : ZMod p)))
    (hinjR : Function.Injective (fun i : Fin I.nC => fun t : Fin (A.J+2) => (R i.val t.val : ZMod p)))
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hPi : (p^(2*K))^r*current maps τ cap I A row L R O Q r K≤(9*pairFactor m F K)^r*U0)
    (hB : p^r*collisions A row L r I.nB≤9^r*n^2)
    (hC : p^r*collisions A row R r I.nC≤9^r*n^2) :
    ∃seed∈admissible (A.J+2) ℓ (TernaryPhysicalDigitSpan.forbidden rows),
      (p^(2*K))^(r+1)*(scale m r K*nextValue maps τ cap I A ℓ row L R O Q r K seed)≤
        scale m r K*(9*pairFactor m F K)^(r+1)*U0 ∧
      p^(r+1)*nextCollision A ℓ row L r I.nB seed≤9^(r+1)*n^2 ∧
      p^(r+1)*nextCollision A ℓ row R r I.nC seed≤9^(r+1)*n^2 := by sorry
