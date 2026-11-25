-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_saturated_e97d455e1e91
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_saturated_e97d455e1e91
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:43.234838+00:00
-- url     : https://prove2.me/theorems/0c3fe57e-2c7b-460e-b3f7-95ba360d96c6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of saturated e97d455e1e91: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of saturated e97d455e1e91
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of saturated e97d455e1e91 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of saturated e97d455e1e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtOfSaturated.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultAtOfSaturated.lean#L12-L16

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_saturated_e97d455e1e91 (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) : Q ∈ J.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_of_saturated» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_saturated_e97d455e1e91
