-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_trace_adjoint__528b3d8d0988
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_trace_adjoint__528b3d8d0988
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:45.670037+00:00
-- url     : https://prove2.me/theorems/c2d35c3a-5e58-50e0-a76e-f6a8d07db86f
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf trace adjoint  528b3d8d0988: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf trace adjoint  528b3d8d0988
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf trace adjoint  528b3d8d0988 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf trace adjoint  528b3d8d0988 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L468-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L468-L473

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_trace_adjoint__528b3d8d0988 (T : H₁ →ₗ[ℂ] H₁) :
    LinearMap.trace ℂ H₁ (LinearMap.adjoint T) = conj (LinearMap.trace ℂ H₁ T) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«trace_adjoint'» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_trace_adjoint__528b3d8d0988
