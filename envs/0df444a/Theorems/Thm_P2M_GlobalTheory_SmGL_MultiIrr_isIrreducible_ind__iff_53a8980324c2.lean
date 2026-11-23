-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2
-- name    : P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:55.140813+00:00
-- url     : https://prove2.me/theorems/e610c94b-4160-48f0-8524-e30ab95e6516
-- title:
--   P2 M Global Theory Sm GL Multi Irr is Irreducible ind  iff 53a8980324c2: P2 M Global Theory Sm GL Multi Irr is Irreducible ind  iff 53a8980324c2
-- statement:
--   The P2 M Global Theory Sm GL Multi Irr is Irreducible ind  iff 53a8980324c2 construction uses the P2 M Global Theory Sm GL Multi Irr is Irreducible ind  iff 53a8980324c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L290-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleIffOfLinearEquiv.lean#L290-L324

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

theorem P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2 (e : a ⊕ b ≃ n) (e' : a' ⊕ b' ≃ n') (ea : a ≃ a') (eb : b ≃ b')
    {ρ : Representation ℂ (GL a k × GL b k) V} {ρ' : Representation ℂ (GL a' k × GL b' k) W} (κ : V ≃ₗ[ℂ] W)
    (h : ∀ g v, κ (ρ g v) = ρ' (relabel k ea g.1, relabel k eb g.2) (κ v)) :
    (ind₂ e ρ).IsIrreducible ↔ (ind₂ e' ρ').IsIrreducible := by sorry

alias «GlobalTheory».«SmGL».«MultiIrr».«isIrreducible_ind₂_iff» := P2M_GlobalTheory_SmGL_MultiIrr_isIrreducible_ind__iff_53a8980324c2
