-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_unit_mul_sub_mem_e9005f30e709
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_unit_mul_sub_mem_e9005f30e709
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:56.089954+00:00
-- url     : https://prove2.me/theorems/75e4e5a7-23fc-461d-9774-85865673c454
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of unit mul sub mem e9005f30e709: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of unit mul sub mem e9005f30e709
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of unit mul sub mem e9005f30e709 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq of unit mul sub mem e9005f30e709 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L127-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L127-L170

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_unit_mul_sub_mem_e9005f30e709 {P W : Ideal (MRing ι R)} (hW : W.IsPrime) {f g u v : MRing ι R}
    (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) : divCycle P f W = divCycle P g W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_of_unit_mul_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_unit_mul_sub_mem_e9005f30e709
