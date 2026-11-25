-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_tail_a426f24c6159
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_tail_a426f24c6159
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:47.609019+00:00
-- url     : https://prove2.me/theorems/e831a78b-35fd-475b-b585-2472951fe569
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega tail a426f24c6159: P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega tail a426f24c6159
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega tail a426f24c6159 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega tail a426f24c6159 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L19-L25

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_tail_a426f24c6159 (h2 : SymplCons.Statement) {n : ℕ} (x y : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    symplOmega (symplTail x) (symplTail y) =
      symplOmega x y - (x (Sum.inr 0) * y (Sum.inl 0) - x (Sum.inl 0) * y (Sum.inr 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceMem».«omega_tail» := P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_tail_a426f24c6159
