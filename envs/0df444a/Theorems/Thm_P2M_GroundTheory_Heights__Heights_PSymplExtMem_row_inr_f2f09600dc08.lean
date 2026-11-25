-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inr_f2f09600dc08
-- name    : P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inr_f2f09600dc08
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:40.989791+00:00
-- url     : https://prove2.me/theorems/9040f3d5-29b6-4689-af0b-bd2e33b2d9e3
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Ext Mem row inr f2f09600dc08: P2 M Ground Theory Heights  Heights PSympl Ext Mem row inr f2f09600dc08
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Ext Mem row inr f2f09600dc08 construction uses the P2 M Ground Theory Heights  Heights PSympl Ext Mem row inr f2f09600dc08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplExtMem.lean#L28-L29

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

theorem P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inr_f2f09600dc08 (i : Fin n) :
    symplExt α β γ δ Q (Sum.inr i.succ) = symplCons 0 0 (Q (Sum.inr i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplExtMem».«row_inr» := P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inr_f2f09600dc08
