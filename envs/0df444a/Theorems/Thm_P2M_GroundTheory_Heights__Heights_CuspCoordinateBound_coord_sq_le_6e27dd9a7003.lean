-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_coord_sq_le_6e27dd9a7003
-- name    : P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_coord_sq_le_6e27dd9a7003
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:04.382241+00:00
-- url     : https://prove2.me/theorems/848a024c-72fd-471c-9aa6-b71f0e4217ac
-- title:
--   P2 M Ground Theory Heights  Heights Cusp Coordinate Bound coord sq le 6e27dd9a7003: P2 M Ground Theory Heights  Heights Cusp Coordinate Bound coord sq le 6e27dd9a7003
-- statement:
--   The P2 M Ground Theory Heights  Heights Cusp Coordinate Bound coord sq le 6e27dd9a7003 construction uses the P2 M Ground Theory Heights  Heights Cusp Coordinate Bound coord sq le 6e27dd9a7003 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCoordinateBound.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PCuspCoordinateBound.lean#L15-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCoordinateBound
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
open GroundTheory.Heights₂.Heights.CuspCoordinateBound

theorem P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_coord_sq_le_6e27dd9a7003 {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (hc : 0 < c)
    (hY : ∀ x : Fin g → ℝ, c * ∑ l, x l ^ 2 ≤ MCSchur.qf Y x) (β : Fin g → ℝ) (k : Fin g) :
    c * β k ^ 2 ≤ MCSchur.qf Y β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CuspCoordinateBound».«coord_sq_le» := P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_coord_sq_le_6e27dd9a7003
