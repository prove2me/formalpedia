-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:34.650586+00:00
-- url     : https://prove2.me/theorems/4218fdb7-0077-4aba-9d6b-5d97feb2a671
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span mul 4461e376663a: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span mul 4461e376663a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span mul 4461e376663a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes sup span mul 4461e376663a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L118-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleMul.lean#L118-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a [IsNoetherianRing A] {P W : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ∉ P) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_sup_span_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a
