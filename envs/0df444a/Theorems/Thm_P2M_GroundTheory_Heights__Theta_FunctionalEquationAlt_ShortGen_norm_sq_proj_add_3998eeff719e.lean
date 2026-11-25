-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_norm_sq_proj_add_3998eeff719e
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_norm_sq_proj_add_3998eeff719e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:27.338465+00:00
-- url     : https://prove2.me/theorems/9eecc64b-d47c-578e-a66c-d27e4ea16bc2
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen norm sq proj add 3998eeff719e: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen norm sq proj add 3998eeff719e
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen norm sq proj add 3998eeff719e construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen norm sq proj add 3998eeff719e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L125-L129

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_norm_sq_proj_add_3998eeff719e (v x : W) (hv : v ≠ 0) (s : ℝ) :
    ‖proj v x + s • v‖ ^ 2 = ‖proj v x‖ ^ 2 + s ^ 2 * ‖v‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«norm_sq_proj_add» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_norm_sq_proj_add_3998eeff719e
