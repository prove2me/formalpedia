-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_integral_cond_linearEquiv_66821f484f1d
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_integral_cond_linearEquiv_66821f484f1d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:03.188472+00:00
-- url     : https://prove2.me/theorems/f174e0de-870e-4b6f-b978-7a55d2fd6dff
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height integral cond linear Equiv 66821f484f1d: P2 M Ground Theory Heights  Heights Objects Height integral cond linear Equiv 66821f484f1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height integral cond linear Equiv 66821f484f1d construction uses the P2 M Ground Theory Heights  Heights Objects Height integral cond linear Equiv 66821f484f1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L397-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L397-L412

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_integral_cond_linearEquiv_66821f484f1d (E : (Fin k × Fin n → ℂ) ≃ₗ[ℝ] (Fin k × Fin n → ℂ))
    (s : Set (Fin k × Fin n → ℂ)) (G : (Fin k × Fin n → ℂ) → ℝ) (hG : Measurable G) :
    ∫ u, G (E u) ∂cond volume (E ⁻¹' s) = ∫ x, G x ∂cond volume s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«integral_cond_linearEquiv» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_integral_cond_linearEquiv_66821f484f1d
