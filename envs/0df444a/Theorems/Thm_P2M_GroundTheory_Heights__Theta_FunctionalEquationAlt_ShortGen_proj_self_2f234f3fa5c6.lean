-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:33:41.595812+00:00
-- url     : https://prove2.me/theorems/6a1fbb85-c3fd-50c9-80d5-dd89cf107bbb
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj self 2f234f3fa5c6: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj self 2f234f3fa5c6
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj self 2f234f3fa5c6 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj self 2f234f3fa5c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L120-L121

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6 (v : W) (hv : v ≠ 0) : proj v v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«proj_self» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
