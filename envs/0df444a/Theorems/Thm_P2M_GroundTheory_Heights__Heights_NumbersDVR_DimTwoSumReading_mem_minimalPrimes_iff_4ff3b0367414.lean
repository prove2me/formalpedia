-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_mem_minimalPrimes_iff_4ff3b0367414
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_mem_minimalPrimes_iff_4ff3b0367414
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:19.509203+00:00
-- url     : https://prove2.me/theorems/d580354c-b637-4a8f-99f9-629036eb6abb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading mem minimal Primes iff 4ff3b0367414: P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading mem minimal Primes iff 4ff3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading mem minimal Primes iff 4ff3b0367414 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading mem minimal Primes iff 4ff3b0367414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L48-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L48-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimTwoSumReading
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
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
variable {A : Type*} [CommRing A]
variable [IsDomain A] [IsNoetherianRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_mem_minimalPrimes_iff_4ff3b0367414 {a : A} (ha : a ≠ 0) (W : Ideal A) [W.IsPrime] :
    W ∈ (Ideal.span {a}).minimalPrimes ↔ W.height = 1 ∧ a ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DimTwoSumReading».«mem_minimalPrimes_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_mem_minimalPrimes_iff_4ff3b0367414
