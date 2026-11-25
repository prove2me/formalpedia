-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mul_mem_sup_span_of_sub_mem_409f1971e60c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mul_mem_sup_span_of_sub_mem_409f1971e60c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:30.143314+00:00
-- url     : https://prove2.me/theorems/03878b22-9ad4-517c-b1fb-49fcdcc88e65
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mul mem sup span of sub mem 409f1971e60c: P2 M Ground Theory Heights  Heights Numbers DVR mul mem sup span of sub mem 409f1971e60c
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mul mem sup span of sub mem 409f1971e60c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mul mem sup span of sub mem 409f1971e60c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L50-L57

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
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mul_mem_sup_span_of_sub_mem_409f1971e60c {P : Ideal A} {f g u v : A} (h : u * f - v * g ∈ P) {x : A}
    (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mul_mem_sup_span_of_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mul_mem_sup_span_of_sub_mem_409f1971e60c
