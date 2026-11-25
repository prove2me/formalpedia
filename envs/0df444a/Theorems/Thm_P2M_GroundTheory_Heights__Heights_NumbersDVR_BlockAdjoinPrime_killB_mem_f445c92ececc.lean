-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_mem_f445c92ececc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_mem_f445c92ececc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:25.790813+00:00
-- url     : https://prove2.me/theorems/47ad8397-87de-5001-a65a-1566653cb282
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B mem f445c92ececc: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B mem f445c92ececc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B mem f445c92ececc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B mem f445c92ececc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L102-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L102-L122

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
variable [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_mem_f445c92ececc {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K)
    {q : MRing ι R} (hq : q ∈ Q) : killB B q ∈ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«killB_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_mem_f445c92ececc
