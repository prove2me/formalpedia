-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_ind__parInd_equiv_f8687141444d
-- name    : P2M_GlobalTheory_SmGL_MultiIrr_ind__parInd_equiv_f8687141444d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:07.845809+00:00
-- url     : https://prove2.me/theorems/d7dccde7-1870-4a16-b834-035fba9e9f84
-- title:
--   P2 M Global Theory Sm GL Multi Irr ind  par Ind equiv f8687141444d: P2 M Global Theory Sm GL Multi Irr ind  par Ind equiv f8687141444d
-- statement:
--   The P2 M Global Theory Sm GL Multi Irr ind  par Ind equiv f8687141444d construction uses the P2 M Global Theory Sm GL Multi Irr ind  par Ind equiv f8687141444d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L389-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L389-L436

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n a' b' n' : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] [Fintype n'] [DecidableEq n']
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

theorem P2M_GlobalTheory_SmGL_MultiIrr_ind__parInd_equiv_f8687141444d (e : (Σ i, m i) ≃ n) (σ₀ : Representation ℂ (GL (m 0) k) V)
    (ρ : Representation ℂ (Levi k fun i : Fin s => m i.succ) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (h : ∀ g x, σ g (κ x) = κ (TensorProduct.map (σ₀ (g 0)) (ρ fun i => g i.succ) x)) :
    Nonempty ((ind₂ ((headTail m).trans e) (extTensor σ₀ (parInd (Equiv.refl _) ρ))).Equiv (parInd e σ)) := by sorry

alias «GlobalTheory».«SmGL».«MultiIrr».«ind₂_parInd_equiv» := P2M_GlobalTheory_SmGL_MultiIrr_ind__parInd_equiv_f8687141444d
