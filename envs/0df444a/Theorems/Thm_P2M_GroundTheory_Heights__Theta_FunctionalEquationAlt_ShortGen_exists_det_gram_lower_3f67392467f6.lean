-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_det_gram_lower_3f67392467f6
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_det_gram_lower_3f67392467f6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:11.627959+00:00
-- url     : https://prove2.me/theorems/f7279993-999f-4a47-82f6-3804d8129044
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists det gram lower 3f67392467f6: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists det gram lower 3f6739
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists det gram lower 3f67392467f6 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists det gram lower 3f67392467f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L416-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L416-L419

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_det_gram_lower_3f67392467f6 {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ∃ g : ℝ, 0 < g ∧ ∀ b : Fin n → W, LinearIndependent ℝ b →
      Sep (span ℤ (Set.range b)) lam → g ≤ (gram ℝ b).det := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«exists_det_gram_lower» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_det_gram_lower_3f67392467f6
