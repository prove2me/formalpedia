-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:04.643429+00:00
-- url     : https://prove2.me/theorems/73857e84-e135-471a-b0d3-204a630448fc
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds log inv sq nonneg b1faa07e0605: P2 M Ground Theory Heights  Heights MCBounds log inv sq nonneg b1faa07e0605
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds log inv sq nonneg b1faa07e0605 construction uses the P2 M Ground Theory Heights  Heights MCBounds log inv sq nonneg b1faa07e0605 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)

theorem P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605 {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ Real.log (‖w‖ ^ 2)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«log_inv_sq_nonneg» := P2M_GroundTheory_Heights__Heights_MCBounds_log_inv_sq_nonneg_b1faa07e0605
