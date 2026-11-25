-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_smulIdeal_mem_8e11f8c73c62
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_smulIdeal_mem_8e11f8c73c62
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:02.823077+00:00
-- url     : https://prove2.me/theorems/f76cacc3-6109-5964-87d2-9305eb686175
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map smul Ideal mem 8e11f8c73c62: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map smul Ideal mem 8e11f8c73c62
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map smul Ideal mem 8e11f8c73c62 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf map smul Ideal mem 8e11f8c73c62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L509-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L509-L519

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
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_smulIdeal_mem_8e11f8c73c62 (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V)
    (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V') (hU : ∀ a ∈ A, U a ∈ B) {x : V}
    (hx : x ∈ smulIdeal aa A) : U x ∈ smulIdeal aa B := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«map_smulIdeal_mem» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_map_smulIdeal_mem_8e11f8c73c62
