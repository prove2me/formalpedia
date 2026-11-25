-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_83a21f1546d0
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_83a21f1546d0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:42.960817+00:00
-- url     : https://prove2.me/theorems/5922af7e-df7c-4289-9d59-8da4c47032ae
-- title:
--   P2 M Ground Theory Heights  Heights MCDet norm det mul sq le 83a21f1546d0: P2 M Ground Theory Heights  Heights MCDet norm det mul sq le 83a21f1546d0
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet norm det mul sq le 83a21f1546d0 construction uses the P2 M Ground Theory Heights  Heights MCDet norm det mul sq le 83a21f1546d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L99-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L99-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_83a21f1546d0 (A B : Matrix m n 𝕜) :
    ‖(Bᴴ * A).det‖ ^ 2 ≤ RCLike.re (Bᴴ * B).det * RCLike.re (Aᴴ * A).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«norm_det_mul_sq_le» := P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_83a21f1546d0
