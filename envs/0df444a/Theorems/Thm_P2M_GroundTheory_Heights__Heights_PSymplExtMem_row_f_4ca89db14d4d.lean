-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_f_4ca89db14d4d
-- name    : P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_f_4ca89db14d4d
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:30.320606+00:00
-- url     : https://prove2.me/theorems/2d03bacb-0f78-4a79-badf-f6e908872090
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Ext Mem row f 4ca89db14d4d: P2 M Ground Theory Heights  Heights PSympl Ext Mem row f 4ca89db14d4d
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Ext Mem row f 4ca89db14d4d construction uses the P2 M Ground Theory Heights  Heights PSympl Ext Mem row f 4ca89db14d4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L23-L23

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

theorem P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_f_4ca89db14d4d : symplExt α β γ δ Q (Sum.inr 0) = symplCons γ δ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplExtMem».«row_f» := P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_f_4ca89db14d4d
