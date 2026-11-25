-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_blockWeight_assocVar_d21f57505629
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_blockWeight_assocVar_d21f57505629
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:36.429682+00:00
-- url     : https://prove2.me/theorems/97abd448-4d18-47b9-a65e-4116647431d7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left block Weight assoc Var d21f57505629: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left block Weight
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left block Weight assoc Var d21f57505629 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left block Weight assoc Var d21f57505629 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L58-L63

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_blockWeight_assocVar_d21f57505629 [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (p : Σ k : K ⊕ K', Sum.elim ι ι' k) (s : K ⊕ (K' ⊕ K₂)) :
    blockWeight (Sum.elim ι (Sum.elim ι' ι₂)) (assocVar ι₂ p) s =
      Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inl k))
        (Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inr k)) 0) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorLeft».«blockWeight_assocVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_blockWeight_assocVar_d21f57505629
