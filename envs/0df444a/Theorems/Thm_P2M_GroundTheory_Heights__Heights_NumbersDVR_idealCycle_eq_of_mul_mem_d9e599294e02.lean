-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_eq_of_mul_mem_d9e599294e02
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_eq_of_mul_mem_d9e599294e02
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:52.110801+00:00
-- url     : https://prove2.me/theorems/0ac38f36-4c8a-4eee-8699-d00c743f14c3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle eq of mul mem d9e599294e02: P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle eq of mul mem d9e599294e02
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle eq of mul mem d9e599294e02 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle eq of mul mem d9e599294e02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivisorIdealCycle.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivisorIdealCycle.lean#L18-L31

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_eq_of_mul_mem_d9e599294e02 {J J' U : Ideal (MRing ι R)} {s t : MRing ι R} (hs : s ∉ U)
    (ht : t ∉ U) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    idealCycle J U = idealCycle J' U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«idealCycle_eq_of_mul_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_eq_of_mul_mem_d9e599294e02
