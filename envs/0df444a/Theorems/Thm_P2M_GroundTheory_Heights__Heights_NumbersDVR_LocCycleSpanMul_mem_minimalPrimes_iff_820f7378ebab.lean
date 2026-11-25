-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_LocCycleSpanMul_mem_minimalPrimes_iff_820f7378ebab
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_LocCycleSpanMul_mem_minimalPrimes_iff_820f7378ebab
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:58.019036+00:00
-- url     : https://prove2.me/theorems/f6905edc-f263-469c-a333-f166516e89e4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Loc Cycle Span Mul mem minimal Primes iff 820f7378ebab: P2 M Ground Theory Heights  Heights Numbers DVR Loc Cycle Span Mul mem minimal Primes iff 820f73
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Loc Cycle Span Mul mem minimal Primes iff 820f7378ebab construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Loc Cycle Span Mul mem minimal Primes iff 820f7378ebab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PLocCycleSpanMul.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PLocCycleSpanMul.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemMinimalPrimesIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocCycleSpanMul
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
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_LocCycleSpanMul_mem_minimalPrimes_iff_820f7378ebab {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«LocCycleSpanMul».«mem_minimalPrimes_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_LocCycleSpanMul_mem_minimalPrimes_iff_820f7378ebab
