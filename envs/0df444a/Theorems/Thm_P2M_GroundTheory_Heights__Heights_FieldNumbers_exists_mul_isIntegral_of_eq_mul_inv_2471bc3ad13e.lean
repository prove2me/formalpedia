-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_mul_isIntegral_of_eq_mul_inv_2471bc3ad13e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_mul_isIntegral_of_eq_mul_inv_2471bc3ad13e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:01.985251+00:00
-- url     : https://prove2.me/theorems/22a94390-058c-4f1d-909d-5aa85b2862c2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists mul is Integral of eq mul inv 2471bc3ad13e: P2 M Ground Theory Heights  Heights Field Numbers exists mul is Integral of eq mul inv 2471bc3ad13e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists mul is Integral of eq mul inv 2471bc3ad13e construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists mul is Integral of eq mul inv 2471bc3ad13e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L15-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/LocalIntegralClosureChart.lean#L15-L38

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_mul_isIntegral_of_eq_mul_inv_2471bc3ad13e {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (R A : Subalgebra F Ω) (hRA : R ≤ A)
    (hloc : ∀ a ∈ A, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ a = r * d⁻¹)
    {x : Ω} (hx : IsIntegral A x) : ∃ d ∈ R, d ≠ 0 ∧ d⁻¹ ∈ A ∧ IsIntegral R (d * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_mul_isIntegral_of_eq_mul_inv» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_mul_isIntegral_of_eq_mul_inv_2471bc3ad13e
