-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_map_bijective_of_saturated_276e2f64ac24
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_map_bijective_of_saturated_276e2f64ac24
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:33.901852+00:00
-- url     : https://prove2.me/theorems/43818370-8945-4136-93f3-de49c96ff947
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR localized Quot map bijective of saturated 276e2f64ac24: P2 M Ground Theory Heights  Heights Numbers DVR localized Quot map bijective of saturated 276e2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR localized Quot map bijective of saturated 276e2f64ac24 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR localized Quot map bijective of saturated 276e2f64ac24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtOfSaturated.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtOfSaturated.lean#L18-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtOfSaturated
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
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_map_bijective_of_saturated_276e2f64ac24 (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) :
    Function.Bijective (LocalizedModule.map Q.primeCompl
      (Submodule.mapQ J Q LinearMap.id (fun _ ha => hJQ ha) : (A ⧸ J) →ₗ[A] A ⧸ Q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«localizedQuot_map_bijective_of_saturated» := P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_map_bijective_of_saturated_276e2f64ac24
