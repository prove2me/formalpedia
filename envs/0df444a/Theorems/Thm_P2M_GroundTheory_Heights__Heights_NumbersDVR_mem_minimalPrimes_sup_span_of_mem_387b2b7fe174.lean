-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_of_mem_387b2b7fe174
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_of_mem_387b2b7fe174
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:20:23.049356+00:00
-- url     : https://prove2.me/theorems/e998d0b7-7dbb-56a3-86d8-943d03c7538e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span of mem 387b2b7fe174: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span of mem 387b2b7fe174
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span of mem 387b2b7fe174 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span of mem 387b2b7fe174 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RelevantMinimalOfDivCycleNeZero.lean#L66-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RelevantMinimalOfDivCycleNeZero.lean#L66-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RelevantMinimalOfDivCycleNeZero
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_of_mem_387b2b7fe174 {A : Type*} [CommRing A] [IsNoetherianRing A] {P H : Ideal A}
    [hP : P.IsPrime] {x y : A} (hH : H ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hy : y ∉ P)
    (hyH : y ∈ H) : H ∈ (P ⊔ Ideal.span {y}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_sup_span_of_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_of_mem_387b2b7fe174
