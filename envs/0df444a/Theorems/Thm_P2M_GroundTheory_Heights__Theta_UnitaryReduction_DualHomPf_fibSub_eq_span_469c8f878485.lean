-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:04.594964+00:00
-- url     : https://prove2.me/theorems/bd66c560-bf6d-5671-9b6a-5542626451b7
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub eq span 469c8f878485: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub eq span 469c8f878485
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub eq span 469c8f878485 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub eq span 469c8f878485 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L367-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L367-L385

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
variable {E : Type} [Field E] [NumberField E]
variable (S : MetSpace E) (τ : InfinitePlace E)

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485 (W : Submodule E S.V) :
    S.fibSub W τ = Submodule.span ℂ (S.pt τ '' (W : Set S.V)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«fibSub_eq_span» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_eq_span_469c8f878485
