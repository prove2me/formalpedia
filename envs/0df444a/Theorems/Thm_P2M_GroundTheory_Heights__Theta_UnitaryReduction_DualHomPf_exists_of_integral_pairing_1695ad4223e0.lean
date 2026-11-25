-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_of_integral_pairing_1695ad4223e0
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_of_integral_pairing_1695ad4223e0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:46.301469+00:00
-- url     : https://prove2.me/theorems/07da7ab1-1122-5187-b518-dfb9f8444700
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists of integral pairing 1695ad4223e0: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists of integral pairing 1695
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists of integral pairing 1695ad4223e0 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists of integral pairing 1695ad4223e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L131-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L131-L208

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
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_of_integral_pairing_1695ad4223e0 (z : InfinitePlace E → ℂ)
    (hz : ∀ c : 𝓞 E, ∃ n : ℤ, ∑ τ : InfinitePlace E, (τ.embedding (c : E) * z τ).re = n) :
    ∃ t : E, (∀ τ, z τ = τ.embedding t) ∧
      t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«exists_of_integral_pairing» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_of_integral_pairing_1695ad4223e0
