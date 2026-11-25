-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_one_le_log_radius_6b216f4bf8bf
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_one_le_log_radius_6b216f4bf8bf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:43.734068+00:00
-- url     : https://prove2.me/theorems/2dae88a6-555b-4dee-a46c-7844fab781a9
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds one le log radius 6b216f4bf8bf: P2 M Ground Theory Heights  Heights MCBounds one le log radius 6b216f4bf8bf
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds one le log radius 6b216f4bf8bf construction uses the P2 M Ground Theory Heights  Heights MCBounds one le log radius 6b216f4bf8bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L34-L36

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_one_le_log_radius_6b216f4bf8bf {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ Real.log (D.radius z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«one_le_log_radius» := P2M_GroundTheory_Heights__Heights_MCBounds_one_le_log_radius_6b216f4bf8bf
