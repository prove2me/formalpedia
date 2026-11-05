-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSignedSelection_native_zero
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection.native_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:14:59.090578+00:00
-- url     : https://prove2.me/theorems/82cefacc-2769-4311-9a63-2f22e277eecf
-- title:
--   native_zero
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSignedSelection.lean#L64-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSignedSelection.lean#L64-L95

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectedTerminal_native_zero

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (K n radix nA : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (X B C : ℕ→ℤ) (catalog : ℕ→ℕ→ℕ→ℕ)

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSignedSelection.native_zero (r M : ℕ) (hr : r≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hbase : 1<radix) (hprime : 2*radix<p) (hcap : 4*U<radix^A.J)
    (hinjB : Function.Injective (fun i : Fin I.nB => B i.val))
    (hinjC : Function.Injective (fun i : Fin I.nC => C i.val))
    (hB : ∀i<I.nB, |B i|≤(U : ℤ)) (hC : ∀i<I.nC, |C i|≤(U : ℤ))
    (hdet : (K+K).factorial*radix^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hnA : nA≤n) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hfactor : 0<9*pairFactor m F K)
    (hdrift : (9*pairFactor m F K)^4*M^(4*K+3)≤(p^(2*K))^4)
    (hcover : n^2≤M^r) (hcarry : (2^A.J)^4*(A.J+2)^(8*K)≤n)
    (hn : ((2*K).factorial*radix^(2*K))^8<n) :
    let s := state maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog r
    WeightedGlobalNativeTensorScore.pairedPotential
      (setup (r := r) maps τ cap Q
        (WeightedGlobalArenaNativeComplete.input I U radix nA (selectedHash A s r) X B C)) K A.J
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.leftRaw U radix A.J (B j)) i)
      (fun j i => TernarySignedLayout.feature (TernarySignedReduction.rightRaw U radix A.J (C j)) i)=0 := by sorry
