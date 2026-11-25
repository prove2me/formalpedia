-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_weight_mapDomain_midVar_b2a63a3b761b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_weight_mapDomain_midVar_b2a63a3b761b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:01.259134+00:00
-- url     : https://prove2.me/theorems/cf12e64b-9c55-40b6-9c64-a038b69d1fcd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right weight map Domain mid Var b2a63a3b761b: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right weight m
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right weight map Domain mid Var b2a63a3b761b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right weight map Domain mid Var b2a63a3b761b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L54-L69

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
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_weight_mapDomain_midVar_b2a63a3b761b [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (Finsupp.mapDomain (midVar ι₂) d) =
      midNat (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«weight_mapDomain_midVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_weight_mapDomain_midVar_b2a63a3b761b
