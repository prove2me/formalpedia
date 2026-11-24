-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:54.588439+00:00
-- url     : https://prove2.me/theorems/b49852e0-7bf7-4957-8c24-2326d33ea257
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of mul mem ff40c44cee89: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of mul mem ff40c44cee89
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of mul mem ff40c44cee89 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of mul mem ff40c44cee89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean#L15-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
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
noncomputable section
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89 {J J' W : Ideal A} {s t : A} (hs : s ∉ W) (ht : t ∉ W)
    (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) (hW : W ∈ J.minimalPrimes) :
    W ∈ J'.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_of_mul_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89
