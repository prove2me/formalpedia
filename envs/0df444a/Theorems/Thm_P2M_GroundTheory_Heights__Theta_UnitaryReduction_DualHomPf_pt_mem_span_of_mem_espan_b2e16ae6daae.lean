-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_span_of_mem_espan_b2e16ae6daae
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_span_of_mem_espan_b2e16ae6daae
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:28.399989+00:00
-- url     : https://prove2.me/theorems/fe0e4846-0a05-4390-80d9-90c971484652
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem span of mem espan b2e16ae6daae: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem span of mem espan b2e16ae6
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem span of mem espan b2e16ae6daae construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf pt mem span of mem espan b2e16ae6daae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L387-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L387-L393

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

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_span_of_mem_espan_b2e16ae6daae (A : Submodule (𝓞 E) S.V) {w : S.V} (hw : w ∈ espan A) :
    S.pt τ w ∈ Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«pt_mem_span_of_mem_espan» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_pt_mem_span_of_mem_espan_b2e16ae6daae
