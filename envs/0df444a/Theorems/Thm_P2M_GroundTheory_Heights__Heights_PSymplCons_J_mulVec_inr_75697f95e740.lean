-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inr_75697f95e740
-- name    : P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inr_75697f95e740
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:24.980888+00:00
-- url     : https://prove2.me/theorems/e20a5f14-9420-48dd-8b0b-ba761f3886a6
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inr 75697f95e740: P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inr 75697f95e740
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inr 75697f95e740 construction uses the P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inr 75697f95e740 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplCons.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplCons.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.PSymplCons

theorem P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inr_75697f95e740 {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inr i) = v (Sum.inl i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplCons».«J_mulVec_inr» := P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inr_75697f95e740
