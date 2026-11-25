-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_log_norm_of_analytic_63c35a4f4a91
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_log_norm_of_analytic_63c35a4f4a91
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:01.326383+00:00
-- url     : https://prove2.me/theorems/3d1c1db1-7f25-45d1-9861-3112a9713755
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh circle Integrable log norm of analytic 63c35a4f4a91: P2 M Ground Theory Heights  Heights MCPsh circle Integrable log norm of analytic 63c35a4f4a91
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh circle Integrable log norm of analytic 63c35a4f4a91 construction uses the P2 M Ground Theory Heights  Heights MCPsh circle Integrable log norm of analytic 63c35a4f4a91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshCore.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshCore.lean#L34-L39

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_log_norm_of_analytic_63c35a4f4a91 {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«circleIntegrable_log_norm_of_analytic» := P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_log_norm_of_analytic_63c35a4f4a91
