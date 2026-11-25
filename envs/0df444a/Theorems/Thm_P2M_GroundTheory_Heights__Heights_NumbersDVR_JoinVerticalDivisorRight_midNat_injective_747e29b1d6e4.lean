-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_midNat_injective_747e29b1d6e4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_midNat_injective_747e29b1d6e4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:19.193985+00:00
-- url     : https://prove2.me/theorems/ad5a9417-71a4-4a91-9c22-79a28c393f8c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mid Nat injective 747e29b1d6e4: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mid Nat injectiv
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mid Nat injective 747e29b1d6e4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right mid Nat injective 747e29b1d6e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_midNat_injective_747e29b1d6e4 : Function.Injective (midNat (K := K) (K' := K') (K₂ := K₂)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«midNat_injective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_midNat_injective_747e29b1d6e4
