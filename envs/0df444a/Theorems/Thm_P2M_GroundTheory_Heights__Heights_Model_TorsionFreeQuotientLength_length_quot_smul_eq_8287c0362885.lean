-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885
-- name    : P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:22.386667+00:00
-- url     : https://prove2.me/theorems/96cd391f-2e1e-46e3-823d-bae4afadfb54
-- title:
--   P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length quot smul eq 8287c0362885: P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length quot smul eq 8287
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length quot smul eq 8287c0362885 construction uses the P2 M Ground Theory Heights  Heights Model Torsion Free Quotient Length length quot smul eq 8287c0362885 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PTorsionFreeQuotientLength.lean#L66-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PTorsionFreeQuotientLength.lean#L66-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885 {N F₀ : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup F₀] [Module R F₀] (φ : F₀ →ₗ[R] N) (hφ : Function.Injective φ) {a : R}
    (hreg : Function.Injective fun x : N => a • x)
    (hfin : IsFiniteLength R (N ⧸ LinearMap.range φ)) :
    Module.length R (N ⧸ (a • ⊤ : Submodule R N)) =
      Module.length R (F₀ ⧸ (a • ⊤ : Submodule R F₀)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«TorsionFreeQuotientLength».«length_quot_smul_eq» := P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885
