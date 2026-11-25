-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_right_3ac668c7eb0d
-- name    : P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_right_3ac668c7eb0d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:53.546834+00:00
-- url     : https://prove2.me/theorems/69fe000c-a6b9-43e5-ba95-75da63c00ebd
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero right 3ac668c7eb0d: P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero right 3ac668c7eb0d
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero right 3ac668c7eb0d construction uses the P2 M Ground Theory Heights  Heights PSympl Ext Mem omega zero right 3ac668c7eb0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L15-L17

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

theorem P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_right_3ac668c7eb0d {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega w (0 : l ⊕ l → R) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplExtMem».«omega_zero_right» := P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_right_3ac668c7eb0d
