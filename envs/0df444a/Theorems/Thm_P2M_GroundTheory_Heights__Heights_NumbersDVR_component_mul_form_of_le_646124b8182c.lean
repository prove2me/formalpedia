-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_le_646124b8182c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_le_646124b8182c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:57.467379+00:00
-- url     : https://prove2.me/theorems/d6dc4c7d-20c0-4095-baa1-1e4392c09efc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR component mul form of le 646124b8182c: P2 M Ground Theory Heights  Heights Numbers DVR component mul form of le 646124b8182c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR component mul form of le 646124b8182c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR component mul form of le 646124b8182c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L81-L87

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_le_646124b8182c {v g : MRing ι R} {β : K → ℕ} (hg : IsMultiHomog g β) {n : K → ℕ}
    (hn : β ≤ n) :
    weightedHomogeneousComponent (blockWeight ι) n (v * g) =
      weightedHomogeneousComponent (blockWeight ι) (n - β) v * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«component_mul_form_of_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_le_646124b8182c
