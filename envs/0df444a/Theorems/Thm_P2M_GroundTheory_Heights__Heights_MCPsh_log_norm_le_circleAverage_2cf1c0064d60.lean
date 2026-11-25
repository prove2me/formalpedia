-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_log_norm_le_circleAverage_2cf1c0064d60
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_log_norm_le_circleAverage_2cf1c0064d60
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:36.581203+00:00
-- url     : https://prove2.me/theorems/e15c0df3-26f1-43fb-88ee-dc9f3f9a8dc4
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh log norm le circle Average 2cf1c0064d60: P2 M Ground Theory Heights  Heights MCPsh log norm le circle Average 2cf1c0064d60
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh log norm le circle Average 2cf1c0064d60 construction uses the P2 M Ground Theory Heights  Heights MCPsh log norm le circle Average 2cf1c0064d60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshCore.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshCore.lean#L11-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
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
open Metric Filter Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCPsh_log_norm_le_circleAverage_2cf1c0064d60 {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (h0 : h 0 ≠ 0) :
    Real.log ‖h 0‖ ≤ circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«log_norm_le_circleAverage» := P2M_GroundTheory_Heights__Heights_MCPsh_log_norm_le_circleAverage_2cf1c0064d60
