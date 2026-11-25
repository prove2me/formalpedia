-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_uniformiser_50f9902254e2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_uniformiser_50f9902254e2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:25.837148+00:00
-- url     : https://prove2.me/theorems/7d5190e1-4037-4ef7-abcd-597977778610
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor uniformiser 50f9902254e2: P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor uniformiser 50f9902254e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor uniformiser 50f9902254e2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor uniformiser 50f9902254e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean#L152-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean#L152-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_uniformiser_50f9902254e2 {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (H : Ideal (MRing ι O)) [H.IsPrime]
    (hϖ : (C ϖ : MRing ι O) ∉ H) :
    IsVerticalDivisor H ϖ 0 (C ϖ) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isVerticalDivisor_uniformiser» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_uniformiser_50f9902254e2
