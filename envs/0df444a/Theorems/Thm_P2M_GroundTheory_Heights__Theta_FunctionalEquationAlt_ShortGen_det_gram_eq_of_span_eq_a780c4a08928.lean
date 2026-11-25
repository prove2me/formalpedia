-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_eq_of_span_eq_a780c4a08928
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_eq_of_span_eq_a780c4a08928
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:05:44.724797+00:00
-- url     : https://prove2.me/theorems/6aafa093-7b1d-4af8-8668-920434f2f7d5
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram eq of span eq a780c4a08928: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram eq of span eq a780
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram eq of span eq a780c4a08928 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram eq of span eq a780c4a08928 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L64-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L64-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [FiniteDimensional ℝ W]

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_eq_of_span_eq_a780c4a08928 {n : ℕ} {b b' : Fin n → W} (hb : LinearIndependent ℤ b)
    (h : span ℤ (Set.range b) = span ℤ (Set.range b')) : (gram ℝ b).det = (gram ℝ b').det := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«det_gram_eq_of_span_eq» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_eq_of_span_eq_a780c4a08928
