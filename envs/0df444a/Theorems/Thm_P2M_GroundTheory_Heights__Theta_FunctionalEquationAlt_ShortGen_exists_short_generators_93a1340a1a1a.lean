-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_short_generators_93a1340a1a1a
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_short_generators_93a1340a1a1a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:06.630465+00:00
-- url     : https://prove2.me/theorems/41b7405a-d468-58b1-8e0a-77c13124db31
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists short generators 93a1340a1a1a: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists short generators 93
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists short generators 93a1340a1a1a construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists short generators 93a1340a1a1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L404-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L404-L414

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_short_generators_93a1340a1a1a {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ R : ℝ, ∀ (n : ℕ) (b : Fin n → W), LinearIndependent ℝ b →
      Sep (span ℤ (Set.range b)) lam → (gram ℝ b).det ≤ C →
      span ℤ (Set.range b) ≤ span ℤ {x | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ R} := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«exists_short_generators» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_short_generators_93a1340a1a1a
