-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:25:06.209922+00:00
-- url     : https://prove2.me/theorems/1f8f1feb-6918-47e2-b0bc-d0fb1dfa46d8
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place eq zero of forall mem minimal Primes 3d9fe51fc8ac: P2 M Ground Theory Heights  Heights Minimal Prime Place eq zero of forall mem minimal Primes
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place eq zero of forall mem minimal Primes 3d9fe51fc8ac construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place eq zero of forall mem minimal Primes 3d9fe51fc8ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L17-L23

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

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac [IsReduced A] {x : A} (h : ∀ q ∈ minimalPrimes A, x ∈ q) :
    x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«eq_zero_of_forall_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac
