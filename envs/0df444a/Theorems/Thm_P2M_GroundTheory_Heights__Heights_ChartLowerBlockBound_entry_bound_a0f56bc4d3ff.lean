-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_entry_bound_a0f56bc4d3ff
-- name    : P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_entry_bound_a0f56bc4d3ff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:19.338888+00:00
-- url     : https://prove2.me/theorems/e4234139-0eaf-499d-a559-57fbc24e9382
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lower Block Bound entry bound a0f56bc4d3ff: P2 M Ground Theory Heights  Heights Chart Lower Block Bound entry bound a0f56bc4d3ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lower Block Bound entry bound a0f56bc4d3ff construction uses the P2 M Ground Theory Heights  Heights Chart Lower Block Bound entry bound a0f56bc4d3ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartLowerHeightsound.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartLowerHeightsound.lean#L21-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartLowerHeightsound
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
open GroundTheory.Heights₂.Heights.ChartLowerBlockBound

theorem P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_entry_bound_a0f56bc4d3ff (D : PeriodChartData) (i l : Fin D.g) :
    ∃ C : ℝ, ∀ p ∈ D.K, ‖D.τ0 p.1 i l‖ ≤ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLowerBlockBound».«entry_bound» := P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_entry_bound_a0f56bc4d3ff
