-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:39.569865+00:00
-- url     : https://prove2.me/theorems/ad062598-6583-4041-a093-ffccdc786b71
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of not mem 1f46edb8b2e2: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of not mem 1f46edb8b2e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of not mem 1f46edb8b2e2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime kill B X of not mem 1f46edb8b2e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L28-L31

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2 (B : Set K) {v : Σ k, ι k} (hv : v.1 ∉ B) :
    killB (R := R) B (X v) = X v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«killB_X_of_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2
