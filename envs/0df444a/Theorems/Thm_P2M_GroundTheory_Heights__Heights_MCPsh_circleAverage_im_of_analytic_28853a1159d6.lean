-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:17.014631+00:00
-- url     : https://prove2.me/theorems/bb76ab71-e2ca-4b49-8ccb-c325a790c191
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh circle Average im of analytic 28853a1159d6: P2 M Ground Theory Heights  Heights MCPsh circle Average im of analytic 28853a1159d6
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh circle Average im of analytic 28853a1159d6 construction uses the P2 M Ground Theory Heights  Heights MCPsh circle Average im of analytic 28853a1159d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6 {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage (fun ζ => (h ζ).im) 0 1 = (h 0).im := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«circleAverage_im_of_analytic» := P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6
