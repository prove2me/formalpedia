-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_continuousOn_f_cb26dcfc3511
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_continuousOn_f_cb26dcfc3511
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:55.438333+00:00
-- url     : https://prove2.me/theorems/9831ec41-8ded-4c2c-901e-2b20aab87bdf
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds continuous On f cb26dcfc3511: P2 M Ground Theory Heights  Heights MCBounds continuous On f cb26dcfc3511
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds continuous On f cb26dcfc3511 construction uses the P2 M Ground Theory Heights  Heights MCBounds continuous On f cb26dcfc3511 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L141-L143

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_continuousOn_f_cb26dcfc3511 : ContinuousOn D.f (D.U ×ˢ D.V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«continuousOn_f» := P2M_GroundTheory_Heights__Heights_MCBounds_continuousOn_f_cb26dcfc3511
