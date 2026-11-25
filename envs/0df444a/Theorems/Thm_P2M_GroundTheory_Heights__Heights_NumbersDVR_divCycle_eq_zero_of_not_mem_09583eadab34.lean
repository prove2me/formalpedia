-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_not_mem_09583eadab34
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_not_mem_09583eadab34
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:55.047248+00:00
-- url     : https://prove2.me/theorems/01cbe2ad-be9d-4c78-aabd-20cd90470bc7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of not mem 09583eadab34: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of not mem 09583eadab34
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of not mem 09583eadab34 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of not mem 09583eadab34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivisorIdealCycle.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivisorIdealCycle.lean#L33-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivisorIdealCycle
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
noncomputable section
universe u
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_not_mem_09583eadab34 {W U : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ U) :
    divCycle W x U = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_zero_of_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_not_mem_09583eadab34
