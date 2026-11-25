-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_inner_proj_6ef07283d6e8
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_inner_proj_6ef07283d6e8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:10:46.706815+00:00
-- url     : https://prove2.me/theorems/3d61994e-7e63-564d-abb1-1663772dfc62
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen inner proj 6ef07283d6e8: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen inner proj 6ef07283d6e8
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen inner proj 6ef07283d6e8 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen inner proj 6ef07283d6e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L108-L111

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_inner_proj_6ef07283d6e8 (v x : W) (hv : v ≠ 0) : inner ℝ v (proj v x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«inner_proj» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_inner_proj_6ef07283d6e8
