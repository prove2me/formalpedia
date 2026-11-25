-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_form_mem_of_smulIdeal_c736a6e4c699
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_form_mem_of_smulIdeal_c736a6e4c699
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:15.542888+00:00
-- url     : https://prove2.me/theorems/3782fb9d-bacb-5256-8ba9-7bb944ee26c0
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf form mem of smul Ideal c736a6e4c699: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf form mem of smul Ideal c736a6e4c699
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf form mem of smul Ideal c736a6e4c699 construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf form mem of smul Ideal c736a6e4c699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L521-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L521-L532

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_form_mem_of_smulIdeal_c736a6e4c699 (aa : FractionalIdeal (𝓞 E)⁰ E) (B : Submodule (𝓞 E) V)
    (ρ : V →ₗ[E] E) (hρ : ∀ b ∈ B, ρ b ∈ Set.range (algebraMap (𝓞 E) E)) {x : V}
    (hx : x ∈ smulIdeal aa B) : ρ x ∈ (aa : Submodule (𝓞 E) E) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«form_mem_of_smulIdeal» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_form_mem_of_smulIdeal_c736a6e4c699
