-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_rename_assocVar_mem_mcIdeal_iff_1e71880a676b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_rename_assocVar_mem_mcIdeal_iff_1e71880a676b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:42.81706+00:00
-- url     : https://prove2.me/theorems/1d9f1af7-9249-426e-aa2a-2be9f125f8ab
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left rename assoc Var mem mc Ideal iff 1e71880a676b: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left re
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left rename assoc Var mem mc Ideal iff 1e71880a676b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Left rename assoc Var mem mc Ideal iff 1e71880a676b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivLeft.lean#L47-L53

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_rename_assocVar_mem_mcIdeal_iff_1e71880a676b (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord z w)) ↔ h ∈ mcIdeal R (joinCoord x z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorLeft».«rename_assocVar_mem_mcIdeal_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorLeft_rename_assocVar_mem_mcIdeal_iff_1e71880a676b
