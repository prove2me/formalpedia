-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_monomial_211997d7462a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_monomial_211997d7462a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:14.158806+00:00
-- url     : https://prove2.me/theorems/34c951b5-21ef-4786-9de5-c09f5b11728f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B monomial 211997d7462a: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B monomial 211997d7462a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B monomial 211997d7462a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B monomial 211997d7462a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L34-L46

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_monomial_211997d7462a (B : Set K) (d : (Σ k, ι k) →₀ ℕ) (a : R) :
    killB (R := R) B (monomial d a) =
      if ∀ v ∈ d.support, v.1 ∉ B then monomial d a else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«killB_monomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_monomial_211997d7462a
