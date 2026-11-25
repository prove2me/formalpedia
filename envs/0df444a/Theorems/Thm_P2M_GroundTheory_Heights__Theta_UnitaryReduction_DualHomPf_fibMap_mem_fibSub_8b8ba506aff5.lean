-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_mem_fibSub_8b8ba506aff5
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_mem_fibSub_8b8ba506aff5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:12.729068+00:00
-- url     : https://prove2.me/theorems/f45cc7ae-1c2f-450a-a0a4-82c99baecb3b
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map mem fib Sub 8b8ba506aff5: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map mem fib Sub 8b8ba506aff5
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map mem fib Sub 8b8ba506aff5 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map mem fib Sub 8b8ba506aff5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L421-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L421-L430

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_mem_fibSub_8b8ba506aff5 (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (W : Submodule E T.V)
    (hφ : ∀ v, φ v ∈ W) (y : S.FibSp τ) : S.fibMap T φ τ y ∈ T.fibSub W τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«fibMap_mem_fibSub» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_mem_fibSub_8b8ba506aff5
