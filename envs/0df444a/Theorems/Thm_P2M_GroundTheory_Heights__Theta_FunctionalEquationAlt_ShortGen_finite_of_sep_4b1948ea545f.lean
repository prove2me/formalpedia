-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_finite_of_sep_4b1948ea545f
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_finite_of_sep_4b1948ea545f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:36.267418+00:00
-- url     : https://prove2.me/theorems/f9687801-7999-4771-98c0-aeaeb61dcf2b
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen finite of sep 4b1948ea545f: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen finite of sep 4b1948ea545f
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen finite of sep 4b1948ea545f construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen finite of sep 4b1948ea545f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L29-L32

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_finite_of_sep_4b1948ea545f {L : Submodule ℤ W} {lam : ℝ} (hlam : 0 < lam) (h : Sep L lam) (r : ℝ) :
    {x : W | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«finite_of_sep» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_finite_of_sep_4b1948ea545f
