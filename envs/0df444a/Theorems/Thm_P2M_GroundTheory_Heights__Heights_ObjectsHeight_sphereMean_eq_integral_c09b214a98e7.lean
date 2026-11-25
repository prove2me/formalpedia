-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:33.973596+00:00
-- url     : https://prove2.me/theorems/18204dc5-a441-4f76-ba5c-60f6aa2f422d
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height sphere Mean eq integral c09b214a98e7: P2 M Ground Theory Heights  Heights Objects Height sphere Mean eq integral c09b214a98e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height sphere Mean eq integral c09b214a98e7 construction uses the P2 M Ground Theory Heights  Heights Objects Height sphere Mean eq integral c09b214a98e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L167-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L167-L319

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7 (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (h : HermNorm n)
    (hh : ∀ u, h.norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) (g : (Fin k × Fin n → ℂ) → ℝ)
    (hg : Measurable g) :
    sphereMean h k g = ∫ u, g u ∂IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«sphereMean_eq_integral» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_sphereMean_eq_integral_c09b214a98e7
