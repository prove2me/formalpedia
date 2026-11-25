-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262
-- name    : P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:18.250229+00:00
-- url     : https://prove2.me/theorems/0407fc91-deaf-4170-bc00-f895f87bbef1
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp sq le inv diag mul qf f52478982262: P2 M Ground Theory Heights  Heights MCCusp sq le inv diag mul qf f52478982262
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp sq le inv diag mul qf f52478982262 construction uses the P2 M Ground Theory Heights  Heights MCCusp sq le inv diag mul qf f52478982262 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L45-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262 {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (x : ι → ℝ) (i : ι) :
    x i ^ 2 ≤ Z⁻¹ i i * qf Z x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCusp».«sq_le_inv_diag_mul_qf» := P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262
