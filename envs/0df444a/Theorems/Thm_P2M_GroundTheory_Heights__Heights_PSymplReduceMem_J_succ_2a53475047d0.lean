-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_2a53475047d0
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_2a53475047d0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:13.335881+00:00
-- url     : https://prove2.me/theorems/ff17e8fa-59f1-4d02-91aa-ce828dd74507
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ 2a53475047d0: P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ 2a53475047d0
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ 2a53475047d0 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ 2a53475047d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_2a53475047d0 {n : ℕ} (a b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) =
      J (Fin n) ℝ a b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceMem».«J_succ» := P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_2a53475047d0
