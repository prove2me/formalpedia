-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_not_le_4feacf11ecb8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_not_le_4feacf11ecb8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:01.098736+00:00
-- url     : https://prove2.me/theorems/d4f6f557-291d-47f8-92c1-b3074e81e0a7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR component mul form of not le 4feacf11ecb8: P2 M Ground Theory Heights  Heights Numbers DVR component mul form of not le 4feacf11ecb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR component mul form of not le 4feacf11ecb8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR component mul form of not le 4feacf11ecb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L89-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_not_le_4feacf11ecb8 {v g : MRing ι R} {β : K → ℕ} (hg : IsMultiHomog g β)
    {n : K → ℕ} (hn : ¬ β ≤ n) :
    weightedHomogeneousComponent (blockWeight ι) n (v * g) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«component_mul_form_of_not_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_not_le_4feacf11ecb8
