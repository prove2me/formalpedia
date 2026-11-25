-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_sub_round_smul_51ee2204c70f
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_sub_round_smul_51ee2204c70f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:34:45.56984+00:00
-- url     : https://prove2.me/theorems/32f805d2-7be5-4209-b252-9f92ef48fd78
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen sub round smul 51ee2204c70f: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen sub round smul 51ee2204c70f
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen sub round smul 51ee2204c70f construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen sub round smul 51ee2204c70f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L133-L137

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_sub_round_smul_51ee2204c70f (v x : W) :
    x - (round (inner ℝ v x / ‖v‖ ^ 2)) • v =
      proj v x + (inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2)) • v := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«sub_round_smul» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_sub_round_smul_51ee2204c70f
