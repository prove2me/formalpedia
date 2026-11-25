-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:06:07.864296+00:00
-- url     : https://prove2.me/theorems/806e67ae-2d82-4e65-a2fc-052eff987ca5
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists finset integral span 73e78e11898a: P2 M Ground Theory Heights  Heights Field Numbers exists finset integral span 73e78e11898a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists finset integral span 73e78e11898a construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists finset integral span 73e78e11898a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L42-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L42-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a (hN : NoetherIntegralClosureFinite.Statement.{u})
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] {S : Set Ω} (hS : S.Finite)
    (A : Subalgebra F Ω) (L : IntermediateField F Ω) (hRA : Algebra.adjoin F S ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ Algebra.adjoin F S, ∃ d ∈ Algebra.adjoin F S,
      d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    (hEL : IntermediateField.adjoin F S ≤ L)
    (hfin : FiniteDimensional (IntermediateField.adjoin F S) (IntermediateField.extendScalars hEL)) :
    ∃ s : Finset Ω, (∀ e ∈ s, e ∈ L ∧ IsIntegral A e) ∧
      ∀ x ∈ L, IsIntegral A x → x ∈ Submodule.span A (s : Set Ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_finset_integral_span» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a
