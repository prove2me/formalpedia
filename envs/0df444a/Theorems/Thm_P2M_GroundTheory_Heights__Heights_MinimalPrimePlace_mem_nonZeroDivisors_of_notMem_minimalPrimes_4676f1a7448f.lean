-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_mem_nonZeroDivisors_of_notMem_minimalPrimes_4676f1a7448f
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_mem_nonZeroDivisors_of_notMem_minimalPrimes_4676f1a7448f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:58.379087+00:00
-- url     : https://prove2.me/theorems/a762375d-79ad-47f7-8fcd-09a196aea3e0
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place mem non Zero Divisors of not Mem minimal Primes 4676f1a7448f: P2 M Ground Theory Heights  Heights Minimal Prime Place mem non Zero Divisors of n
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place mem non Zero Divisors of not Mem minimal Primes 4676f1a7448f construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place mem non Zero Divisors of not Mem minimal Primes 4676f1a7448f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L25-L30

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

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_mem_nonZeroDivisors_of_notMem_minimalPrimes_4676f1a7448f [IsReduced A] {w : A}
    (hw : ∀ q ∈ minimalPrimes A, w ∉ q) : w ∈ nonZeroDivisors A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«mem_nonZeroDivisors_of_notMem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_mem_nonZeroDivisors_of_notMem_minimalPrimes_4676f1a7448f
