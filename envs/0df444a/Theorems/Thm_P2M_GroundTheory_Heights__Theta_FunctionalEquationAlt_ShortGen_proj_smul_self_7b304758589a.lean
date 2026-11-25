-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_smul_self_7b304758589a
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_smul_self_7b304758589a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:36.270353+00:00
-- url     : https://prove2.me/theorems/52df4dc2-be36-4715-adda-399c3fc82c97
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj smul self 7b304758589a: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj smul self 7b304758589a
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj smul self 7b304758589a construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen proj smul self 7b304758589a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L114-L117

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_smul_self_7b304758589a (v : W) (t : ℝ) (hv : v ≠ 0) : proj v (t • v) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«proj_smul_self» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_smul_self_7b304758589a
