-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_e_6d67875bd178
-- name    : P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_e_6d67875bd178
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:54.233306+00:00
-- url     : https://prove2.me/theorems/7a729348-a41e-493b-9a73-85eced928b15
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Ext Mem row e 6d67875bd178: P2 M Ground Theory Heights  Heights PSympl Ext Mem row e 6d67875bd178
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Ext Mem row e 6d67875bd178 construction uses the P2 M Ground Theory Heights  Heights PSympl Ext Mem row e 6d67875bd178 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L21-L21

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

theorem P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_e_6d67875bd178 : symplExt α β γ δ Q (Sum.inl 0) = symplCons α β 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplExtMem».«row_e» := P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_e_6d67875bd178
