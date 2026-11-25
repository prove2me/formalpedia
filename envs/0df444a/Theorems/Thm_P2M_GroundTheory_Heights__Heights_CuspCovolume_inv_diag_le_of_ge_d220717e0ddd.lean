-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCovolume_inv_diag_le_of_ge_d220717e0ddd
-- name    : P2M_GroundTheory_Heights__Heights_CuspCovolume_inv_diag_le_of_ge_d220717e0ddd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:20.796572+00:00
-- url     : https://prove2.me/theorems/3e43d56e-d608-4fa7-b8f9-c9cabdc0affe
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Covolume inv diag le of ge d220717e0ddd: P2 M Ground Theory Heights  Heights Cusp Covolume inv diag le of ge d220717e0ddd
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Covolume inv diag le of ge d220717e0ddd construction uses the P2 M Ground Theory Heights  Heights Cusp Covolume inv diag le of ge d220717e0ddd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCovolume.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCovolume.lean#L33-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCovolume
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
noncomputable section
open GroundTheory.Heights₂.Heights.CuspCovolume

theorem P2M_GroundTheory_Heights__Heights_CuspCovolume_inv_diag_le_of_ge_d220717e0ddd {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {c : ℝ}
    (hc : 0 < c) (h : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf Y x) (k : Fin g) :
    Y⁻¹ k k ≤ 1 / c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspCovolume».«inv_diag_le_of_ge» := P2M_GroundTheory_Heights__Heights_CuspCovolume_inv_diag_le_of_ge_d220717e0ddd
