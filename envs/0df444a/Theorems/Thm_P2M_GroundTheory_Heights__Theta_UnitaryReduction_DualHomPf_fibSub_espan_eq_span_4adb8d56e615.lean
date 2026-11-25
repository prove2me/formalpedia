-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_espan_eq_span_4adb8d56e615
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_espan_eq_span_4adb8d56e615
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:07:18.962831+00:00
-- url     : https://prove2.me/theorems/25c0f4a1-fe42-49cd-88e5-ddb4e188f588
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub espan eq span 4adb8d56e615: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub espan eq span 4adb8d56e615
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub espan eq span 4adb8d56e615 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Sub espan eq span 4adb8d56e615 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L395-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L395-L400

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_espan_eq_span_4adb8d56e615 (A : Submodule (𝓞 E) S.V) :
    S.fibSub (espan A) τ = Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«fibSub_espan_eq_span» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibSub_espan_eq_span_4adb8d56e615
