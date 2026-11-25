-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_Stages_ind__assoc_9f771f8b94ce
-- name    : P2M_GlobalTheory_SmGL_Stages_ind__assoc_9f771f8b94ce
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:06.208802+00:00
-- url     : https://prove2.me/theorems/2bd1df30-25b8-4e55-9c33-f967ea18402c
-- title:
--   P2 M Global Theory Sm GL Stages ind  assoc 9f771f8b94ce: P2 M Global Theory Sm GL Stages ind  assoc 9f771f8b94ce
-- statement:
--   The P2 M Global Theory Sm GL Stages ind  assoc 9f771f8b94ce construction uses the P2 M Global Theory Sm GL Stages ind  assoc 9f771f8b94ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L371-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean#L371-L415

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

theorem P2M_GlobalTheory_SmGL_Stages_ind__assoc_9f771f8b94ce (e₁ : ab ⊕ c ≃ n) (f₁ : a ⊕ b ≃ ab) (e₂ : a ⊕ bc ≃ n) (f₂ : b ⊕ c ≃ bc)
    (Ha : ∀ i, e₁ (.inl (f₁ (.inl i))) = e₂ (.inl i))
    (Hb : ∀ i, e₁ (.inl (f₁ (.inr i))) = e₂ (.inr (f₂ (.inl i))))
    (Hc : ∀ i, e₁ (.inr i) = e₂ (.inr (f₂ (.inr i))))
    (π₁ : Representation ℂ (GL a k) V₁) (π₂ : Representation ℂ (GL b k) V₂)
    (π₃ : Representation ℂ (GL c k) V₃) :
    Nonempty ((ind₂ e₁ (extTensor (ind₂ f₁ (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ e₂ (extTensor π₁ (ind₂ f₂ (extTensor π₂ π₃))))) := by sorry

alias «GlobalTheory».«SmGL».«Stages».«ind₂_assoc» := P2M_GlobalTheory_SmGL_Stages_ind__assoc_9f771f8b94ce
