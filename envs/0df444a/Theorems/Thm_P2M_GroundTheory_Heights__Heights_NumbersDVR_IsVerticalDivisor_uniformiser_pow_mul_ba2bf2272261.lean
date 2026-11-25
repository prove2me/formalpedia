-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_uniformiser_pow_mul_ba2bf2272261
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_uniformiser_pow_mul_ba2bf2272261
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:30.730707+00:00
-- url     : https://prove2.me/theorems/696c5aff-3445-44b3-a850-9135c3fc638d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor uniformiser pow mul ba2bf2272261: P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor uniformiser pow mul ba2bf22722
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor uniformiser pow mul ba2bf2272261 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Is Vertical Divisor uniformiser pow mul ba2bf2272261 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByEffectiveDivisor.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByEffectiveDivisor.lean#L14-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByEffectiveDivisor
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_uniformiser_pow_mul_ba2bf2272261 {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IsVerticalDivisor».«uniformiser_pow_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_uniformiser_pow_mul_ba2bf2272261
