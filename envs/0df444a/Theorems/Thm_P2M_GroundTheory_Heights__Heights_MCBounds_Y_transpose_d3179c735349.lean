-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_Y_transpose_d3179c735349
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_Y_transpose_d3179c735349
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:42.345586+00:00
-- url     : https://prove2.me/theorems/733941db-d4da-4cab-8a0f-620cab9706c3
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds Y transpose d3179c735349: P2 M Ground Theory Heights  Heights MCBounds Y transpose d3179c735349
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds Y transpose d3179c735349 construction uses the P2 M Ground Theory Heights  Heights MCBounds Y transpose d3179c735349 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L58-L65

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_Y_transpose_d3179c735349 {z : Fin D.n → ℂ} (hz : z ∈ D.U) : (D.Y z)ᵀ = D.Y z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«Y_transpose» := P2M_GroundTheory_Heights__Heights_MCBounds_Y_transpose_d3179c735349
