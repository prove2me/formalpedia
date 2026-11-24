-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:03.006045+00:00
-- url     : https://prove2.me/theorems/1c86d38f-4fc9-473b-b5c1-ecf346b627ff
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR component mul form add f298b0f9964b: P2 M Ground Theory Heights  Heights Numbers DVR component mul form add f298b0f9964b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR component mul form add f298b0f9964b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR component mul form add f298b0f9964b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L66-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L66-L79

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b {u f : MRing ι R} {α : K → ℕ} (hf : IsMultiHomog f α) (γ : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) (γ + α) (u * f) =
      weightedHomogeneousComponent (blockWeight ι) γ u * f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«component_mul_form_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b
