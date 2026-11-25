-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_fibSub_0741dd921c5a
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_fibSub_0741dd921c5a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:20.715364+00:00
-- url     : https://prove2.me/theorems/ccfa42f5-64b6-5d54-ad64-bdc5a299e1a4
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map fib Sub 0741dd921c5a: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map fib Sub 0741dd921c5a
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map fib Sub 0741dd921c5a construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf fib Map fib Sub 0741dd921c5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L559-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L559-L569

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_fibSub_0741dd921c5a (S T : MetSpace E) (τ : InfinitePlace E) (φ : S.V →ₗ[E] T.V)
    (W : Submodule E S.V) (W' : Submodule E T.V) (hφ : ∀ w ∈ W, φ w ∈ W') {y : S.FibSp τ}
    (hy : y ∈ S.fibSub W τ) : S.fibMap T φ τ y ∈ T.fibSub W' τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«fibMap_fibSub» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_fibMap_fibSub_0741dd921c5a
