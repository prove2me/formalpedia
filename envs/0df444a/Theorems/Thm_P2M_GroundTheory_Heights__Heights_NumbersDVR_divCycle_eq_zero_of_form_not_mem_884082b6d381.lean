-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_form_not_mem_884082b6d381
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_form_not_mem_884082b6d381
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:36.767569+00:00
-- url     : https://prove2.me/theorems/d6e9bf85-fb42-571f-824b-11738e9887ed
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of form not mem 884082b6d381: P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of form not mem 884082b6d381
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of form not mem 884082b6d381 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR div Cycle eq zero of form not mem 884082b6d381 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleEqZeroOfFormNotMem.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/DivCycleEqZeroOfFormNotMem.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleEqZeroOfFormNotMem
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
universe u
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_form_not_mem_884082b6d381 (P : Ideal (MRing ι R)) {x : MRing ι R} {W : Ideal (MRing ι R)}
    (hx : x ∉ W) : divCycle P x W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«divCycle_eq_zero_of_form_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_form_not_mem_884082b6d381
