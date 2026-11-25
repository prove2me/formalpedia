-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_max_mem_minimalPrimes_49103e6a00fd
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_max_mem_minimalPrimes_49103e6a00fd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:03.341987+00:00
-- url     : https://prove2.me/theorems/160b67d1-baa1-4b17-8cf0-05f48d45e035
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading max mem minimal Primes 49103e6a00fd: P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading max mem minimal Primes 4910
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading max mem minimal Primes 49103e6a00fd construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading max mem minimal Primes 49103e6a00fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L74-L92

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
omit [IsDomain A] [IsNoetherianRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_max_mem_minimalPrimes_49103e6a00fd [IsLocalRing A] (h2 : ringKrullDim A = 2) (W : Ideal A) [hW : W.IsPrime]
    (h1 : W.height = 1) {b : A} (hbW : b ∉ W) (hbm : b ∈ maximalIdeal A) :
    maximalIdeal A ∈ (W ⊔ Ideal.span {b}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DimTwoSumReading».«max_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_max_mem_minimalPrimes_49103e6a00fd
