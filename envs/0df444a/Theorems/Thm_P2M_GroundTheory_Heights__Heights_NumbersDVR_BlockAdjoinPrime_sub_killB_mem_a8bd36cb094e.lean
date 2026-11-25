-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sub_killB_mem_a8bd36cb094e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sub_killB_mem_a8bd36cb094e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:27.922101+00:00
-- url     : https://prove2.me/theorems/833eb695-655e-4548-a12d-abbe56f2b65d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sub kill B mem a8bd36cb094e: P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sub kill B mem a8bd36cb094e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sub kill B mem a8bd36cb094e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Block Adjoin Prime sub kill B mem a8bd36cb094e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L62-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlockAdjoinPrime.lean#L62-L79

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sub_killB_mem_a8bd36cb094e (B : Set K) (p : MRing ι R) : p - killB B p ∈ varIdeal (R := R) B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlockAdjoinPrime».«sub_killB_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sub_killB_mem_a8bd36cb094e
