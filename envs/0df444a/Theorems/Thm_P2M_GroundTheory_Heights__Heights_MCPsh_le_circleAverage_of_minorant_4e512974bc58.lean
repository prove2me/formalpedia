-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_le_circleAverage_of_minorant_4e512974bc58
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_le_circleAverage_of_minorant_4e512974bc58
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:53.360256+00:00
-- url     : https://prove2.me/theorems/58da1f0b-bc7d-4a5a-b6c6-02d9e7b2bb2f
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh le circle Average of minorant 4e512974bc58: P2 M Ground Theory Heights  Heights MCPsh le circle Average of minorant 4e512974bc58
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh le circle Average of minorant 4e512974bc58 construction uses the P2 M Ground Theory Heights  Heights MCPsh le circle Average of minorant 4e512974bc58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshCore.lean#L41-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshCore.lean#L41-L79

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

theorem P2M_GroundTheory_Heights__Heights_MCPsh_le_circleAverage_of_minorant_4e512974bc58 {φ ℓ : ℂ → ℝ} {h : ℂ → ℂ} {ℓ0 : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) (h0 : h 0 ≠ 0)
    (hφ : CircleIntegrable φ 0 1) (hℓ : CircleIntegrable ℓ 0 1)
    (hpt : ∀ ζ ∈ sphere (0:ℂ) 1, h ζ ≠ 0 → 2 * Real.log ‖h ζ‖ - ℓ ζ ≤ φ ζ)
    (hℓavg : circleAverage ℓ 0 1 ≤ ℓ0) (hφ0 : φ 0 ≤ 2 * Real.log ‖h 0‖ - ℓ0) :
    φ 0 ≤ circleAverage φ 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«le_circleAverage_of_minorant» := P2M_GroundTheory_Heights__Heights_MCPsh_le_circleAverage_of_minorant_4e512974bc58
