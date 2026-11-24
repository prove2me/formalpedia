-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
-- name    : P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:15.061796+00:00
-- url     : https://prove2.me/theorems/525bd216-d425-488c-bef0-dd12149ffe7c
-- title:
--   P2 M Global Theory Sm GL Multi Irr is Irreducible ind  c2ad73a9489a: P2 M Global Theory Sm GL Multi Irr is Irreducible ind  c2ad73a9489a
-- statement:
--   The P2 M Global Theory Sm GL Multi Irr is Irreducible ind  c2ad73a9489a construction uses the P2 M Global Theory Sm GL Multi Irr is Irreducible ind  c2ad73a9489a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L326-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L326-L339

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
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

theorem P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a (H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ e (extTensor π₁ π₂)).IsIrreducible := by sorry

alias «GlobalTheory».«SmGL».«MultiIrr».«isIrreducible_ind₂» := P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__c2ad73a9489a
