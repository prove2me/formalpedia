-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_apply_bc8e45da2f5a
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_apply_bc8e45da2f5a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:39:25.088062+00:00
-- url     : https://prove2.me/theorems/cc05ecfb-46f7-4d96-89bd-30cbe9be9aba
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj apply bc8e45da2f5a: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj apply bc8e45da2f5a
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj apply bc8e45da2f5a construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj apply bc8e45da2f5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L104-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L104-L104

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_apply_bc8e45da2f5a (v x : W) : proj v x = x - (inner ℝ v x / ‖v‖ ^ 2) • v := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«proj_apply» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_apply_bc8e45da2f5a
