-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_analyticOnNhd_det_c705e943e556
-- name    : P2M_GroundTheory_Heights__Heights_MCPsh_analyticOnNhd_det_c705e943e556
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:34.523016+00:00
-- url     : https://prove2.me/theorems/823807c8-8a8d-526d-b191-b9c1020d0407
-- title:
--   P2 M Ground Theory Heights  Heights MCPsh analytic On Nhd det c705e943e556: P2 M Ground Theory Heights  Heights MCPsh analytic On Nhd det c705e943e556
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPsh analytic On Nhd det c705e943e556 construction uses the P2 M Ground Theory Heights  Heights MCPsh analytic On Nhd det c705e943e556 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PshMatrix.lean#L97-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix
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
open Matrix Metric Real
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem P2M_GroundTheory_Heights__Heights_MCPsh_analyticOnNhd_det_c705e943e556 {s : Set ℂ} {M : ℂ → Matrix κ κ ℂ}
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun ζ => M ζ i j) s) :
    AnalyticOnNhd ℂ (fun ζ => (M ζ).det) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPsh».«analyticOnNhd_det» := P2M_GroundTheory_Heights__Heights_MCPsh_analyticOnNhd_det_c705e943e556
