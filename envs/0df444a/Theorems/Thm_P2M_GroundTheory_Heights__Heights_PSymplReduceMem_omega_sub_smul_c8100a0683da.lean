-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_sub_smul_c8100a0683da
-- name    : P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_sub_smul_c8100a0683da
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:29.089882+00:00
-- url     : https://prove2.me/theorems/44c63159-361e-46c7-ac8c-4e870afe9a6a
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega sub smul c8100a0683da: P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega sub smul c8100a0683da
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega sub smul c8100a0683da construction uses the P2 M Ground Theory Heights  Heights PSympl Reduce Mem omega sub smul c8100a0683da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplReduceMem.lean#L11-L17

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

theorem P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_sub_smul_c8100a0683da {l : Type} [Fintype l] [DecidableEq l] (u v w : l ⊕ l → ℝ) (c d : ℝ) :
    symplOmega (u - c • w) (v - d • w) =
      symplOmega u v - d * symplOmega u w - c * symplOmega w v + c * d * symplOmega w w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplReduceMem».«omega_sub_smul» := P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_sub_smul_c8100a0683da
