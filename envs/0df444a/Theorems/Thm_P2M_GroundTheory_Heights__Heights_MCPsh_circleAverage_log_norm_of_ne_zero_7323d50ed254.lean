-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_log_norm_of_ne_zero_7323d50ed254
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_log_norm_of_ne_zero_7323d50ed254
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:04.585038+00:00
-- url     : https://prove2.me/theorems/c83c15c5-108a-48c1-8ce9-29a08dc1b210
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh circle Average log norm of ne zero 7323d50ed254: P2 M Ground Theory Heights  Heights MCPsh circle Average log norm of ne zero 7323d50ed254
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh circle Average log norm of ne zero 7323d50ed254 construction uses the P2 M Ground Theory Heights  Heights MCPsh circle Average log norm of ne zero 7323d50ed254 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L28-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Metric Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_log_norm_of_ne_zero_7323d50ed254 {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hne : ∀ ζ ∈ closedBall (0:ℂ) 1, h ζ ≠ 0) :
    circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 = Real.log ‖h 0‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«circleAverage_log_norm_of_ne_zero» := P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_log_norm_of_ne_zero_7323d50ed254
