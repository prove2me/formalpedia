-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_cusp_norm_lt_b55c72d768a7
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_cusp_norm_lt_b55c72d768a7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:21.364846+00:00
-- url     : https://prove2.me/theorems/a3e9562d-efa9-4306-88ef-2c23e61ba139
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds cusp norm lt b55c72d768a7: P2 M Ground Theory Heights  Heights MCBounds cusp norm lt b55c72d768a7
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds cusp norm lt b55c72d768a7 construction uses the P2 M Ground Theory Heights  Heights MCBounds cusp norm lt b55c72d768a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L16-L18

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_cusp_norm_lt_b55c72d768a7 {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    ‖cuspCoord D.a_le z j‖ < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«cusp_norm_lt» := P2M_GroundTheory_Heights__Heights_MCBounds_cusp_norm_lt_b55c72d768a7
