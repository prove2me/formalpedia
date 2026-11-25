-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_e_succ_ad8be0cda494
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_e_succ_ad8be0cda494
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:46.976024+00:00
-- url     : https://prove2.me/theorems/5edf2df9-d89b-489c-8075-51ae70b94d91
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Mem J e succ ad8be0cda494: P2 M Ground Theory Heights  Heights PSympl Reduce Mem J e succ ad8be0cda494
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Mem J e succ ad8be0cda494 construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Mem J e succ ad8be0cda494 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L36-L38

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_e_succ_ad8be0cda494 {n : ℕ} (b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceMem».«J_e_succ» := P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_e_succ_ad8be0cda494
