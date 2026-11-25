-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplOrbit_smul_symplCons_a513fc6e72e3
-- name    : P2M_GroundTheory_Heights__Heights_PSymplOrbit_smul_symplCons_a513fc6e72e3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:00.665195+00:00
-- url     : https://prove2.me/theorems/5a4dfd0c-dcb7-4d86-805a-a6a02fd6a0a2
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Orbit smul sympl Cons a513fc6e72e3: P2 M Ground Theory Heights  Heights PSympl Orbit smul sympl Cons a513fc6e72e3
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Orbit smul sympl Cons a513fc6e72e3 construction uses the P2 M Ground Theory Heights  Heights PSympl Orbit smul sympl Cons a513fc6e72e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplOrbit.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplOrbit.lean#L11-L14

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

theorem P2M_GroundTheory_Heights__Heights_PSymplOrbit_smul_symplCons_a513fc6e72e3 {R : Type*} [CommRing R] {n : ℕ} (m p q : R) (w : Fin n ⊕ Fin n → R) :
    m • symplCons p q w = symplCons (m * p) (m * q) (m • w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplOrbit».«smul_symplCons» := P2M_GroundTheory_Heights__Heights_PSymplOrbit_smul_symplCons_a513fc6e72e3
