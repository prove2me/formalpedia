-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_coeff_killB_d6e25e411cc0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_coeff_killB_d6e25e411cc0
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:40.807803+00:00
-- url     : https://prove2.me/theorems/8969a117-ea1a-4fa8-8a71-8d9e3c8a098c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime coeff kill B d6e25e411cc0: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime coeff kill B d6e25e411cc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime coeff kill B d6e25e411cc0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime coeff kill B d6e25e411cc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L49-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
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
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
open Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_coeff_killB_d6e25e411cc0 (B : Set K) (p : MRing ι R) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (killB B p) = if ∀ v ∈ d.support, v.1 ∉ B then coeff d p else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«coeff_killB» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_coeff_killB_d6e25e411cc0
