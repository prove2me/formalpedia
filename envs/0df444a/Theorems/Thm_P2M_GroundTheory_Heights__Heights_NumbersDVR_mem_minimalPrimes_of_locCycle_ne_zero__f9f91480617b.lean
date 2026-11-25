-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_locCycle_ne_zero__f9f91480617b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_locCycle_ne_zero__f9f91480617b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:30.187519+00:00
-- url     : https://prove2.me/theorems/fcd92b5e-c9bc-4e74-a1f5-63d51df1e70d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of loc Cycle ne zero  f9f91480617b: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of loc Cycle ne zero  f9f91480
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of loc Cycle ne zero  f9f91480617b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of loc Cycle ne zero  f9f91480617b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PLocalCoeffLocal.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PLocalCoeffLocal.lean#L12-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalCoeffLocal
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
open ReciprocityTheory.ChartRestriction.G.AI
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_locCycle_ne_zero__f9f91480617b {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_of_locCycle_ne_zero'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_locCycle_ne_zero__f9f91480617b
