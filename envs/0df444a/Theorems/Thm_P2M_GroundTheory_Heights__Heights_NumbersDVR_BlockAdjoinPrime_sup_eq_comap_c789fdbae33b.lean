-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sup_eq_comap_c789fdbae33b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sup_eq_comap_c789fdbae33b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:31.491714+00:00
-- url     : https://prove2.me/theorems/87fafba3-cbca-54df-9d58-8a08c01f109c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sup eq comap c789fdbae33b: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sup eq comap c789fdbae33b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sup eq comap c789fdbae33b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sup eq comap c789fdbae33b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L124-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L124-L136

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sup_eq_comap_c789fdbae33b {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K) :
    Q ⊔ varIdeal B = Q.comap (killB B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«sup_eq_comap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sup_eq_comap_c789fdbae33b
