-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_mem_minimalPrimes_iff_5f70c654c603
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_mem_minimalPrimes_iff_5f70c654c603
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:28.824803+00:00
-- url     : https://prove2.me/theorems/3ad1074b-605b-4e78-93b7-8ec9674b0f1d
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle mem minimal Primes iff 5f70c654c603: P2 M Ground Theory Heights  Heights Section Cycle mem minimal Primes iff 5f70c654c603
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle mem minimal Primes iff 5f70c654c603 construction uses the P2 M Ground Theory Heights  Heights Section Cycle mem minimal Primes iff 5f70c654c603 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L54-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {S : Type*} [CommRing S]

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_mem_minimalPrimes_iff_5f70c654c603 {J J₁ W : Ideal S} (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) : W ∈ J.minimalPrimes ↔ W ∈ J₁.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«mem_minimalPrimes_iff» := P2M_GroundTheory_Heights__Heights_SectionCycle_mem_minimalPrimes_iff_5f70c654c603
