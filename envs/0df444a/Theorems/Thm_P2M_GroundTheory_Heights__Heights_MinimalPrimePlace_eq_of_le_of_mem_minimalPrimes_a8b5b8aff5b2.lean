-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_of_le_of_mem_minimalPrimes_a8b5b8aff5b2
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_of_le_of_mem_minimalPrimes_a8b5b8aff5b2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:15.957798+00:00
-- url     : https://prove2.me/theorems/7bf83267-6810-4337-b921-bb6dd78d5bb1
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place eq of le of mem minimal Primes a8b5b8aff5b2: P2 M Ground Theory Heights  Heights Minimal Prime Place eq of le of mem minimal Primes a8b5b8aff5b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place eq of le of mem minimal Primes a8b5b8aff5b2 construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place eq of le of mem minimal Primes a8b5b8aff5b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_of_le_of_mem_minimalPrimes_a8b5b8aff5b2 {q q' : Ideal A} (hq : q ∈ minimalPrimes A) (hq' : q' ∈ minimalPrimes A)
    (h : q ≤ q') : q = q' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«eq_of_le_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_of_le_of_mem_minimalPrimes_a8b5b8aff5b2
