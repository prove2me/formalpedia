-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5
-- name    : P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:11.718019+00:00
-- url     : https://prove2.me/theorems/240b3ec9-2eaf-4abd-a9b1-d0527d1ba591
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp inv diag le 31afacab59f5: P2 M Ground Theory Heights  Heights MCCusp inv diag le 31afacab59f5
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp inv diag le 31afacab59f5 construction uses the P2 M Ground Theory Heights  Heights MCCusp inv diag le 31afacab59f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L60-L73

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

theorem P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5 {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (i : ι) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, ε * x i ^ 2 ≤ qf Z x) : Z⁻¹ i i ≤ 1 / ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCusp».«inv_diag_le» := P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5
