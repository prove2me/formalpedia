-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_mem_mcIdeal_iff_89bb1dd42917
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_mem_mcIdeal_iff_89bb1dd42917
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:24.721008+00:00
-- url     : https://prove2.me/theorems/10060bff-c754-4eed-b0d7-d3369a82402a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename mem mc Ideal iff 89bb1dd42917: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename mem mc Ideal iff 89bb1dd42917 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right rename mem mc Ideal iff 89bb1dd42917 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L43-L49

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_mem_mcIdeal_iff_89bb1dd42917 (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord w z)) ↔ h ∈ mcIdeal R (joinCoord x z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«rename_mem_mcIdeal_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_mem_mcIdeal_iff_89bb1dd42917
