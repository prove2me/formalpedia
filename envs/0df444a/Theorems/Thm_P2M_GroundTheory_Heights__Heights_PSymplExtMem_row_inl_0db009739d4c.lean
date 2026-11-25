-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inl_0db009739d4c
-- name    : P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inl_0db009739d4c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:54.914649+00:00
-- url     : https://prove2.me/theorems/1c07cf3d-2af8-5a18-9971-73d7a7fc0f58
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Ext Mem row inl 0db009739d4c: P2 M Ground Theory Heights  Heights PSympl Ext Mem row inl 0db009739d4c
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Ext Mem row inl 0db009739d4c construction uses the P2 M Ground Theory Heights  Heights PSympl Ext Mem row inl 0db009739d4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L25-L26

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
variable {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)

theorem P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inl_0db009739d4c (i : Fin n) :
    symplExt α β γ δ Q (Sum.inl i.succ) = symplCons 0 0 (Q (Sum.inl i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplExtMem».«row_inl» := P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inl_0db009739d4c
