-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_divCycle_ne_zero_77d65d882a25
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_divCycle_ne_zero_77d65d882a25
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:10.32299+00:00
-- url     : https://prove2.me/theorems/5617207a-c88d-46b9-ac4a-d3d8f2d93b88
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of div Cycle ne zero 77d65d882a25: P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of div Cycle ne zero 77d65d882a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of div Cycle ne zero 77d65d882a25 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mem minimal Primes of div Cycle ne zero 77d65d882a25 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_divCycle_ne_zero_77d65d882a25 {K : Type*} {ι : K → Type*} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«mem_minimalPrimes_of_divCycle_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_divCycle_ne_zero_77d65d882a25
