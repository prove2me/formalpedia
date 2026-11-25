-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_assocVar_fst_7150b4a0bfd9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_assocVar_fst_7150b4a0bfd9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:25.164708+00:00
-- url     : https://prove2.me/theorems/c19b9d22-16a0-44eb-a7f7-57a38b6d4c57
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left assoc Var fst 7150b4a0bfd9: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left assoc Var fst 7150b4a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left assoc Var fst 7150b4a0bfd9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left assoc Var fst 7150b4a0bfd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_assocVar_fst_7150b4a0bfd9 (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    (assocVar ι₂ p).1 = Sum.map id Sum.inl p.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorLeft».«assocVar_fst» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_assocVar_fst_7150b4a0bfd9
