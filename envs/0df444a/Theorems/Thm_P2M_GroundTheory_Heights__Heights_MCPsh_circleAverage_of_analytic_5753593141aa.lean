-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_of_analytic_5753593141aa
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_of_analytic_5753593141aa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:44.42656+00:00
-- url     : https://prove2.me/theorems/64b104f2-b1c3-54b1-af33-8a6b9acb7d12
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh circle Average of analytic 5753593141aa: P2 M Ground Theory Heights  Heights MCPsh circle Average of analytic 5753593141aa
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh circle Average of analytic 5753593141aa construction uses the P2 M Ground Theory Heights  Heights MCPsh circle Average of analytic 5753593141aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L11-L16

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_of_analytic_5753593141aa {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage h 0 1 = h 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«circleAverage_of_analytic» := P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_of_analytic_5753593141aa
