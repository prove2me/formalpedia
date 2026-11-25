-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_of_posDef_b8853d9e2e1b
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_of_posDef_b8853d9e2e1b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:24.387221+00:00
-- url     : https://prove2.me/theorems/3332aa4c-79a7-5b66-b42f-5167a61c95ac
-- title:
--   P2 M Ground Theory Heights  Heights MCDet norm det mul sq le of pos Def b8853d9e2e1b: P2 M Ground Theory Heights  Heights MCDet norm det mul sq le of pos Def b8853d9e2e1b
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet norm det mul sq le of pos Def b8853d9e2e1b construction uses the P2 M Ground Theory Heights  Heights MCDet norm det mul sq le of pos Def b8853d9e2e1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L148-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L148-L173

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

theorem P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_of_posDef_b8853d9e2e1b [DecidableEq m] {M : Matrix m m 𝕜} (hM : M.PosDef)
    (F W : Matrix m n 𝕜) :
    ‖(Wᴴ * F).det‖ ^ 2 ≤ RCLike.re (Wᴴ * M * W).det * RCLike.re (Fᴴ * M⁻¹ * F).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«norm_det_mul_sq_le_of_posDef» := P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_of_posDef_b8853d9e2e1b
