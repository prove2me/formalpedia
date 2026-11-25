-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_dualBasis_51edd028661f
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_dualBasis_51edd028661f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:36.853205+00:00
-- url     : https://prove2.me/theorems/c1cbe946-30eb-44af-9132-28545534b067
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists dual Basis 51edd028661f: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists dual Basis 51edd028661f
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists dual Basis 51edd028661f construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf exists dual Basis 51edd028661f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L292-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L292-L338

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
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_dualBasis_51edd028661f (A : Submodule (𝓞 E) V) (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → V) (σ : Fin n → (V →ₗ[E] E)),
      (∀ i, a i ∈ A) ∧ (∀ i, ∀ x ∈ A, σ i x ∈ Set.range (algebraMap (𝓞 E) E)) ∧
      ∀ x ∈ espan A, x = ∑ i, σ i x • a i := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«exists_dualBasis» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_dualBasis_51edd028661f
