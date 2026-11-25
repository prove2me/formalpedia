-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_eqOn_fibSub_e5866ef00b00
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_eqOn_fibSub_e5866ef00b00
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:07:46.150316+00:00
-- url     : https://prove2.me/theorems/beebe9f5-41fe-4621-a666-c4b75affcad1
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf eq On fib Sub e5866ef00b00: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf eq On fib Sub e5866ef00b00
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf eq On fib Sub e5866ef00b00 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf eq On fib Sub e5866ef00b00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L571-L580
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L571-L580

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_eqOn_fibSub_e5866ef00b00 (S : MetSpace E) (τ : InfinitePlace E) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : Submodule (𝓞 E) S.V) {X Y : S.FibSp τ →ₗ[ℂ] M}
    (h : ∀ a ∈ A, X (S.pt τ a) = Y (S.pt τ a)) {x : S.FibSp τ}
    (hx : x ∈ S.fibSub (espan A) τ) : X x = Y x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«eqOn_fibSub» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_eqOn_fibSub_e5866ef00b00
