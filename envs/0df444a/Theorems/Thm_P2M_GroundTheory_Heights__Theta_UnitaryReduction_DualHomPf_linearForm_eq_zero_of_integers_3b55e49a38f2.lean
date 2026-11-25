-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_linearForm_eq_zero_of_integers_3b55e49a38f2
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_linearForm_eq_zero_of_integers_3b55e49a38f2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:20.548713+00:00
-- url     : https://prove2.me/theorems/d1391d0d-265b-5f19-89d1-1c15a59a3f49
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf linear Form eq zero of integers 3b55e49a38f2: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf linear Form eq zero of int
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf linear Form eq zero of integers 3b55e49a38f2 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf linear Form eq zero of integers 3b55e49a38f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L72-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L72-L95

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
open Classical

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_linearForm_eq_zero_of_integers_3b55e49a38f2 (Λ : (InfinitePlace E → ℂ) →ₗ[ℝ] ℝ)
    (h : ∀ c : 𝓞 E, Λ (fun τ => τ.embedding (c : E)) = 0) (w : InfinitePlace E → ℂ) :
    Λ w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«linearForm_eq_zero_of_integers» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_linearForm_eq_zero_of_integers_3b55e49a38f2
