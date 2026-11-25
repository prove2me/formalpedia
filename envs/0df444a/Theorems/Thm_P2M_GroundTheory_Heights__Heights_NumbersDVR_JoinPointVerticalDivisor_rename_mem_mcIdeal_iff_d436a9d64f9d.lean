-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_mem_mcIdeal_iff_d436a9d64f9d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_mem_mcIdeal_iff_d436a9d64f9d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:52.661341+00:00
-- url     : https://prove2.me/theorems/1f6de82f-b217-4185-a5e2-3af2d8963e64
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename mem mc Ideal iff d436a9d64f9d: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename mem mc Ideal iff d436a9d64f9d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor rename mem mc Ideal iff d436a9d64f9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_mem_mcIdeal_iff_d436a9d64f9d (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') h ∈ mcIdeal R (joinCoord y z) ↔ h ∈ mcIdeal R y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointVerticalDivisor».«rename_mem_mcIdeal_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_mem_mcIdeal_iff_d436a9d64f9d
