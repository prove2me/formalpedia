-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplOrbit_symplCons_one_zero_81f42b193b60
-- name    : P2M_GroundTheory_Heights__Heights_PSymplOrbit_symplCons_one_zero_81f42b193b60
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:55.560799+00:00
-- url     : https://prove2.me/theorems/94fbb063-3628-48f0-82aa-92e26b93a889
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Orbit sympl Cons one zero 81f42b193b60: P2 M Ground Theory Heights  Heights PSympl Orbit sympl Cons one zero 81f42b193b60
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Orbit sympl Cons one zero 81f42b193b60 construction uses the P2 M Ground Theory Heights  Heights PSympl Orbit sympl Cons one zero 81f42b193b60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplOrbit.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplOrbit.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplOrbit
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
open GroundTheory.Heights₂.Heights.PSymplOrbit

theorem P2M_GroundTheory_Heights__Heights_PSymplOrbit_symplCons_one_zero_81f42b193b60 {R : Type*} [CommRing R] {n : ℕ} :
    symplCons (1 : R) 0 (0 : Fin n ⊕ Fin n → R) = Pi.single (Sum.inl 0) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplOrbit».«symplCons_one_zero» := P2M_GroundTheory_Heights__Heights_PSymplOrbit_symplCons_one_zero_81f42b193b60
