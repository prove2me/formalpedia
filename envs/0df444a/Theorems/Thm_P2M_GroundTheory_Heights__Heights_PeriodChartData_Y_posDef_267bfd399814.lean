-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PeriodChartData_Y_posDef_267bfd399814
-- name    : P2M_GroundTheory_Heights__Heights_PeriodChartData_Y_posDef_267bfd399814
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:20.668813+00:00
-- url     : https://prove2.me/theorems/e832165e-2862-47dd-8927-89d1f9c5a0a2
-- title:
--   P2 M Ground Theory Heights  Heights Period Chart Data Y pos Def 267bfd399814: P2 M Ground Theory Heights  Heights Period Chart Data Y pos Def 267bfd399814
-- statement:
--   The P2 M Ground Theory Heights  Heights Period Chart Data Y pos Def 267bfd399814 construction uses the P2 M Ground Theory Heights  Heights Period Chart Data Y pos Def 267bfd399814 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartPotentialPsh.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartPotentialPsh.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartPotentialPsh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Metric Real MCPsh
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_PeriodChartData_Y_posDef_267bfd399814 (D : PeriodChartData) {z : Fin D.n → ℂ} (hz : z ∈ D.Ustar) :
    (D.Y z).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PeriodChartData».«Y_posDef» := P2M_GroundTheory_Heights__Heights_PeriodChartData_Y_posDef_267bfd399814
