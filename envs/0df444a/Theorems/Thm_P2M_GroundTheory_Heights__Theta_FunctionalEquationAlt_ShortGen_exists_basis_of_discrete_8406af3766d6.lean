-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_basis_of_discrete_8406af3766d6
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_basis_of_discrete_8406af3766d6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:24.08617+00:00
-- url     : https://prove2.me/theorems/24d154fd-3d9b-5c1f-9710-a12066cfd246
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists basis of discrete 8406af3766d6: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists basis of discrete
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists basis of discrete 8406af3766d6 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen exists basis of discrete 8406af3766d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L40-L51

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_basis_of_discrete_8406af3766d6 (L : Submodule ℤ W) [DiscreteTopology L] :
    ∃ (n : ℕ) (c : Fin n → W), LinearIndependent ℝ c ∧ span ℤ (Set.range c) = L := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«exists_basis_of_discrete» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_basis_of_discrete_8406af3766d6
