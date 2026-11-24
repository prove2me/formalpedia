-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:37.933146+00:00
-- url     : https://prove2.me/theorems/904542df-cbd7-47ae-9fa3-83088f4a6c38
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of mem f7bd28ee701b: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of mem f7bd28ee701b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of mem f7bd28ee701b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of mem f7bd28ee701b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L23-L26

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b (B : Set K) {v : Σ k, ι k} (hv : v.1 ∈ B) :
    killB (R := R) B (X v) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«killB_X_of_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b
