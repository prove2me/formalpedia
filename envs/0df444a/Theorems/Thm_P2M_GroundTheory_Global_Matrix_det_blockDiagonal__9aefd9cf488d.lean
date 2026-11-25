-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_Matrix_det_blockDiagonal__9aefd9cf488d
-- name    : P2M_GroundTheory_Global_Matrix_det_blockDiagonal__9aefd9cf488d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:17.203142+00:00
-- url     : https://prove2.me/theorems/8d64a165-f0f7-4d10-917e-2a9727201ca2
-- title:
--   P2 M Ground Theory Global Matrix det block Diagonal  9aefd9cf488d: P2 M Ground Theory Global Matrix det block Diagonal  9aefd9cf488d
-- statement:
--   The P2 M Ground Theory Global Matrix det block Diagonal  9aefd9cf488d construction uses the P2 M Ground Theory Global Matrix det block Diagonal  9aefd9cf488d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L12-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.Matrix

theorem P2M_GroundTheory_Global_Matrix_det_blockDiagonal__9aefd9cf488d {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (M : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by sorry

alias «GroundTheory».«Global».«Matrix».«det_blockDiagonal'» := P2M_GroundTheory_Global_Matrix_det_blockDiagonal__9aefd9cf488d
