-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSignedSelection_budget
-- name    : ThreeSum.WeightedGlobalArenaSignedSelection.budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:59:57.608194+00:00
-- url     : https://prove2.me/theorems/26469a99-d9b8-43c9-8ca2-03b59c8cd9fc
-- title:
--   Weighted Global Arena Signed Selection: budget
-- statement:
--   All signed-input side conditions of the deterministic real selector
--   follow from the original bounded distinct source integers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSignedSelection.lean#L35-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSignedSelection.lean#L35-L59

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSignedSelection
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

theorem ThreeSum.WeightedGlobalArenaSignedSelection.budget (stop : ℕ) (hstop : stop≤A.J) (hℓ : ℓ≠0) (hp : 3≤p)
    (hbase : 1<radix) (hprime : 2*radix<p) (hcap : 4*U<radix^A.J)
    (hinjB : Function.Injective (fun i : Fin I.nB => B i.val))
    (hinjC : Function.Injective (fun i : Fin I.nC => C i.val))
    (hB : ∀i<I.nB, |B i|≤(U : ℤ)) (hC : ∀i<I.nC, |C i|≤(U : ℤ))
    (hdet : (K+K).factorial*radix^(K+K)<p)
    (hsize1 : 8*(A.J+2)*p^2≤Fintype.card E)
    (hsize : 8*(A.J+2)*p^(2*(K+K))≤Fintype.card E)
    (hnB : I.nB≤n) (hnC : I.nC≤n) :
    ∀j≤stop, Budget maps τ cap Q (base I A.J nA) A K n (initialBudget A K n radix nA)
      (left U radix A.J B) (right U radix A.J C) (requester U radix A.J X) j
      (state maps τ cap U V scoreBound Q I A K n radix nA e ℓ X B C catalog j) := by sorry
