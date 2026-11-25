-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PivotBounds_qf_submatrix_castLE_b2a7fe345f16
-- name    : P2M_GroundTheory_Heights__Heights_PivotBounds_qf_submatrix_castLE_b2a7fe345f16
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:20.943687+00:00
-- url     : https://prove2.me/theorems/9fc5339f-9103-4008-bbce-df082ad439fd
-- title:
--   P2 M Ground Theory Heights  Heights Pivot Bounds qf submatrix cast LE b2a7fe345f16: P2 M Ground Theory Heights  Heights Pivot Bounds qf submatrix cast LE b2a7fe345f16
-- statement:
--   The P2 M Ground Theory Heights  Heights Pivot Bounds qf submatrix cast LE b2a7fe345f16 construction uses the P2 M Ground Theory Heights  Heights Pivot Bounds qf submatrix cast LE b2a7fe345f16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPivotBounds.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPivotBounds.lean#L15-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotBounds
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
open GroundTheory.Heights₂.Heights.PivotBounds

theorem P2M_GroundTheory_Heights__Heights_PivotBounds_qf_submatrix_castLE_b2a7fe345f16 {d m : ℕ} (h : m ≤ d) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin m → ℝ) :
    MCSchur.qf (S.submatrix (Fin.castLE h) (Fin.castLE h)) x =
      MCSchur.qf S (Function.extend (Fin.castLE h) x 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PivotBounds».«qf_submatrix_castLE» := P2M_GroundTheory_Heights__Heights_PivotBounds_qf_submatrix_castLE_b2a7fe345f16
