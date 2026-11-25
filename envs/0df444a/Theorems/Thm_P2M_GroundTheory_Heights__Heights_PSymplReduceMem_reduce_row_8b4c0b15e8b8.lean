-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_reduce_row_8b4c0b15e8b8
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceMem_reduce_row_8b4c0b15e8b8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:59.863037+00:00
-- url     : https://prove2.me/theorems/59d5b1f7-22b5-4f04-91bd-4f052e12a58c
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Mem reduce row 8b4c0b15e8b8: P2 M Ground Theory Heights  Heights PSympl Reduce Mem reduce row 8b4c0b15e8b8
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Mem reduce row 8b4c0b15e8b8 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Mem reduce row 8b4c0b15e8b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L40-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceMem
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
open GroundTheory.Heights₂.Heights.PSymplReduceMem

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceMem_reduce_row_8b4c0b15e8b8 {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (a : Fin n ⊕ Fin n) :
    symplReduce H a = symplTail (H (Sum.map Fin.succ Fin.succ a)) -
      (H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / H (Sum.inl 0) (Sum.inl 0)) •
        symplTail (H (Sum.inl 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceMem».«reduce_row» := P2M_GroundTheory_Heights__Heights_PSymplReduceMem_reduce_row_8b4c0b15e8b8
