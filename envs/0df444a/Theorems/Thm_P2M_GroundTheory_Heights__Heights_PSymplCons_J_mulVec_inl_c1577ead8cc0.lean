-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inl_c1577ead8cc0
-- name    : P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inl_c1577ead8cc0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:24.351954+00:00
-- url     : https://prove2.me/theorems/da5acb69-d3b8-46d5-92cf-3fdf54a0ec6a
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inl c1577ead8cc0: P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inl c1577ead8cc0
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inl c1577ead8cc0 construction uses the P2 M Ground Theory Heights  Heights PSympl Cons J mul Vec inl c1577ead8cc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplCons.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplCons.lean#L11-L13

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

theorem P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inl_c1577ead8cc0 {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inl i) = -v (Sum.inr i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplCons».«J_mulVec_inl» := P2M_GroundTheory_Heights__Heights_PSymplCons_J_mulVec_inl_c1577ead8cc0
