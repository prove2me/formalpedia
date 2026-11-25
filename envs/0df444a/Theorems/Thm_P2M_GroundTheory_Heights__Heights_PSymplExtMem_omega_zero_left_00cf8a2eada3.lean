-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_left_00cf8a2eada3
-- name    : P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_left_00cf8a2eada3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:39.522464+00:00
-- url     : https://prove2.me/theorems/e049edd7-795c-49d4-af4b-67d1aafa6ce9
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero left 00cf8a2eada3: P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero left 00cf8a2eada3
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero left 00cf8a2eada3 construction uses the P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero left 00cf8a2eada3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplExtMem
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
open GroundTheory.Heights₂.Heights.PSymplExtMem

theorem P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_left_00cf8a2eada3 {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega (0 : l ⊕ l → R) w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplExtMem».«omega_zero_left» := P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_left_00cf8a2eada3
