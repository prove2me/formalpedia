-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_weightedHomogeneousComponent_7266b1e936a1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_weightedHomogeneousComponent_7266b1e936a1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:32.845489+00:00
-- url     : https://prove2.me/theorems/dbc243d5-69dc-4dc2-930e-e9fdc7287f15
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename weighted Homogeneous Component 7266b1e936a1: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Ri
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename weighted Homogeneous Component 7266b1e936a1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename weighted Homogeneous Component 7266b1e936a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L89-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L89-L106

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_weightedHomogeneousComponent_7266b1e936a1 [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (b : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (midNat b)
        (rename (midVar ι₂) h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«rename_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_weightedHomogeneousComponent_7266b1e936a1
