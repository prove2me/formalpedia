-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_re_trace_comp_adjoint_67c90ea6f5af
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_re_trace_comp_adjoint_67c90ea6f5af
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:51.870467+00:00
-- url     : https://prove2.me/theorems/f818a058-f515-56f1-a288-d033d8c6b864
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf re trace comp adjoint 67c90ea6f5af: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf re trace comp adjoint 67c90ea6f5af
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf re trace comp adjoint 67c90ea6f5af construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf re trace comp adjoint 67c90ea6f5af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L475-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L475-L486

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_re_trace_comp_adjoint_67c90ea6f5af (X Y : H₁ →ₗ[ℂ] H₂) :
    (LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y)).re =
      (LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X)).re := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«re_trace_comp_adjoint» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_re_trace_comp_adjoint_67c90ea6f5af
