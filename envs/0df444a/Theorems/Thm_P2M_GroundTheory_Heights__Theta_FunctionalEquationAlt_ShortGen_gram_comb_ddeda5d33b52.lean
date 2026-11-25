-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:11:38.612833+00:00
-- url     : https://prove2.me/theorems/1fb1c8ee-1e03-4036-a637-967aaa4b65b5
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen gram comb ddeda5d33b52: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen gram comb ddeda5d33b52
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen gram comb ddeda5d33b52 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen gram comb ddeda5d33b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L55-L60

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52 {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℝ) (b : l → W) :
    gram ℝ (fun i => ∑ j, A i j • b j) = A * gram ℝ b * Aᵀ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«gram_comb» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52
