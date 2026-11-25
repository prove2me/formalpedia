-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_of_analytic_6254991e7596
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_of_analytic_6254991e7596
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:10.503082+00:00
-- url     : https://prove2.me/theorems/0176567a-85f7-4aba-b974-b68bb44c8a30
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh circle Integrable of analytic 6254991e7596: P2 M Ground Theory Heights  Heights MCPsh circle Integrable of analytic 6254991e7596
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh circle Integrable of analytic 6254991e7596 construction uses the P2 M Ground Theory Heights  Heights MCPsh circle Integrable of analytic 6254991e7596 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMean.lean#L18-L20

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_of_analytic_6254991e7596 {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable h 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«circleIntegrable_of_analytic» := P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_of_analytic_6254991e7596
