-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:05.444477+00:00
-- url     : https://prove2.me/theorems/5b36e622-7465-4d8e-8380-cf7ac576c8f1
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds one le radius 6e45f36c6393: P2 M Ground Theory Heights  Heights MCBounds one le radius 6e45f36c6393
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds one le radius 6e45f36c6393 construction uses the P2 M Ground Theory Heights  Heights MCBounds one le radius 6e45f36c6393 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L29-L32

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393 {z : Fin D.n → ℂ} (hz : z ∈ D.U) : 1 ≤ D.radius z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«one_le_radius» := P2M_GroundTheory_Heights__Heights_MCBounds_one_le_radius_6e45f36c6393
