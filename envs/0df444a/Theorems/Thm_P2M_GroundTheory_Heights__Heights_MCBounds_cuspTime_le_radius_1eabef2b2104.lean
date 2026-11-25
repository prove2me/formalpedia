-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_cuspTime_le_radius_1eabef2b2104
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_cuspTime_le_radius_1eabef2b2104
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:03.654615+00:00
-- url     : https://prove2.me/theorems/530edfb6-8756-4530-93cd-a30c6c82c5cd
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds cusp Time le radius 1eabef2b2104: P2 M Ground Theory Heights  Heights MCBounds cusp Time le radius 1eabef2b2104
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds cusp Time le radius 1eabef2b2104 construction uses the P2 M Ground Theory Heights  Heights MCBounds cusp Time le radius 1eabef2b2104 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L38-L56

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_cuspTime_le_radius_1eabef2b2104 {z : Fin D.n → ℂ} (hz : z ∈ D.U) (j : Fin D.a) :
    cuspTime D.a_le z j ≤ D.radius z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«cuspTime_le_radius» := P2M_GroundTheory_Heights__Heights_MCBounds_cuspTime_le_radius_1eabef2b2104
