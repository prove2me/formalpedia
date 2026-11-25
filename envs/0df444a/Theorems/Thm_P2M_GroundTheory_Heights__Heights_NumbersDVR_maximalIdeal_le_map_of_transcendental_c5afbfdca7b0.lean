-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_maximalIdeal_le_map_of_transcendental_c5afbfdca7b0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_maximalIdeal_le_map_of_transcendental_c5afbfdca7b0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:57.372854+00:00
-- url     : https://prove2.me/theorems/639f4f02-14ba-40ac-b4a8-5c8d59920dbd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR maximal Ideal le map of transcendental c5afbfdca7b0: P2 M Ground Theory Heights  Heights Numbers DVR maximal Ideal le map of transcendental c5afbfdca7b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR maximal Ideal le map of transcendental c5afbfdca7b0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR maximal Ideal le map of transcendental c5afbfdca7b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L15-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpLocalChart.lean#L15-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_maximalIdeal_le_map_of_transcendental_c5afbfdca7b0 {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D]
    (hdim : ringKrullDim D ≤ 1) (C : Subring D) (w : D)
    (hinj : Function.Injective (Polynomial.eval₂RingHom C.subtype w))
    (hsurj : ∀ d : D, ∃ a b : Polynomial C,
      Polynomial.eval₂RingHom C.subtype w b ∉ IsLocalRing.maximalIdeal D ∧
      Polynomial.eval₂RingHom C.subtype w b * d = Polynomial.eval₂RingHom C.subtype w a)
    (c₀ : C) (hc₀ : (c₀ : D) ≠ 0) (hc₀m : (c₀ : D) ∈ IsLocalRing.maximalIdeal D) :
    IsLocalRing.maximalIdeal D ≤
      ((IsLocalRing.maximalIdeal D).comap C.subtype).map C.subtype := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«maximalIdeal_le_map_of_transcendental» := P2M_GroundTheory_Heights__Heights_NumbersDVR_maximalIdeal_le_map_of_transcendental_c5afbfdca7b0
