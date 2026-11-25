-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_e_dec9e46caacf
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_e_dec9e46caacf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:13:50.027883+00:00
-- url     : https://prove2.me/theorems/43811c9a-7f60-447f-b918-7f68f9e5441b
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ e dec9e46caacf: P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ e dec9e46caacf
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ e dec9e46caacf construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Mem J succ e dec9e46caacf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L32-L34

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_e_dec9e46caacf {n : ℕ} (a : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceMem».«J_succ_e» := P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_e_dec9e46caacf
