-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_linearIndependent_real_of_int_75b3dfee45d3
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_linearIndependent_real_of_int_75b3dfee45d3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:38.999341+00:00
-- url     : https://prove2.me/theorems/9a2b5791-4c77-4722-bf8e-49ae1ea474dd
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen linear Independent real of int 75b3dfee45d3: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen linear Independent
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen linear Independent real of int 75b3dfee45d3 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen linear Independent real of int 75b3dfee45d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L34-L38

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_linearIndependent_real_of_int_75b3dfee45d3 {n : ℕ} {b : Fin n → W} (hb : LinearIndependent ℤ b)
    (hd : DiscreteTopology (span ℤ (Set.range b))) : LinearIndependent ℝ b := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«linearIndependent_real_of_int» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_linearIndependent_real_of_int_75b3dfee45d3
