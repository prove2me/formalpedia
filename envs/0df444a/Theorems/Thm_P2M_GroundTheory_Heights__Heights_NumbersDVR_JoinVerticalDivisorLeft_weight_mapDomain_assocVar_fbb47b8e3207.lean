-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_weight_mapDomain_assocVar_fbb47b8e3207
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_weight_mapDomain_assocVar_fbb47b8e3207
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:44.637442+00:00
-- url     : https://prove2.me/theorems/4a58a73f-373d-40db-be95-f6858b744557
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left weight map Domain assoc Var fbb47b8e3207: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left weight m
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left weight map Domain assoc Var fbb47b8e3207 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left weight map Domain assoc Var fbb47b8e3207 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L68-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivLeft
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_assocVar_b75e0e1aca5e

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]
omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_weight_mapDomain_assocVar_fbb47b8e3207 [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι' ι₂))) (Finsupp.mapDomain (assocVar ι₂) d) =
      Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
        (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorLeft».«weight_mapDomain_assocVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_weight_mapDomain_assocVar_fbb47b8e3207
