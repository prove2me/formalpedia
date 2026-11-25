-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplCons_symplOmega_eq_sum_d38ace7a12fb
-- name    : P2M_GroundTheory_Heights__Heights_PSymplCons_symplOmega_eq_sum_d38ace7a12fb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:40.447694+00:00
-- url     : https://prove2.me/theorems/3ed25354-e008-494e-8c8e-c92ca0bc6390
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Cons sympl Omega eq sum d38ace7a12fb: P2 M Ground Theory Heights  Heights PSympl Cons sympl Omega eq sum d38ace7a12fb
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Cons sympl Omega eq sum d38ace7a12fb construction uses the P2 M Ground Theory Heights  Heights PSympl Cons sympl Omega eq sum d38ace7a12fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplCons.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplCons.lean#L19-L26

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

theorem P2M_GroundTheory_Heights__Heights_PSymplCons_symplOmega_eq_sum_d38ace7a12fb {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) :
    symplOmega u v = ∑ i, (u (Sum.inr i) * v (Sum.inl i) - u (Sum.inl i) * v (Sum.inr i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplCons».«symplOmega_eq_sum» := P2M_GroundTheory_Heights__Heights_PSymplCons_symplOmega_eq_sum_d38ace7a12fb
