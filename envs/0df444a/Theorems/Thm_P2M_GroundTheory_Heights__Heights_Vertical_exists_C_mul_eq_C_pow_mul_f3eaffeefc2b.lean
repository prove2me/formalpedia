-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_exists_C_mul_eq_C_pow_mul_f3eaffeefc2b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_exists_C_mul_eq_C_pow_mul_f3eaffeefc2b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:25.213881+00:00
-- url     : https://prove2.me/theorems/7ce32cc1-193e-416c-bf83-58f542f4e1c7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical exists C mul eq C pow mul f3eaffeefc2b: P2 M Ground Theory Heights  Heights Vertical exists C mul eq C pow mul f3eaffeefc2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical exists C mul eq C pow mul f3eaffeefc2b construction uses the P2 M Ground Theory Heights  Heights Vertical exists C mul eq C pow mul f3eaffeefc2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean#L16-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

theorem P2M_GroundTheory_Heights__Heights_Vertical_exists_C_mul_eq_C_pow_mul_f3eaffeefc2b {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«exists_C_mul_eq_C_pow_mul» := P2M_GroundTheory_Heights__Heights_Vertical_exists_C_mul_eq_C_pow_mul_f3eaffeefc2b
