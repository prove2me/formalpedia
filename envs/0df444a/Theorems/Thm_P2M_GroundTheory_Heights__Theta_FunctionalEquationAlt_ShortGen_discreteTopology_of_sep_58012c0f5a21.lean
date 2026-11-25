-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:10:41.267221+00:00
-- url     : https://prove2.me/theorems/956919a6-8783-57d3-be9f-9fb57c324912
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen discrete Topology of sep 58012c0f5a21: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen discrete Topology of sep
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen discrete Topology of sep 58012c0f5a21 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen discrete Topology of sep 58012c0f5a21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L21-L27

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
omit [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21 {L : Submodule ℤ W} {lam : ℝ} (hlam : 0 < lam) (h : Sep L lam) :
    DiscreteTopology L := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«discreteTopology_of_sep» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21
