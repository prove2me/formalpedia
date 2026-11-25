-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartGradient_u_eq_daf79c38bffd
-- name    : P2M_GroundTheory_Heights__Heights_MCChartGradient_u_eq_daf79c38bffd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:45:51.483199+00:00
-- url     : https://prove2.me/theorems/bac720d8-2a67-40c7-829a-408acede75fc
-- title:
--   P2 M Ground Theory Heights  Heights MCChart Gradient u eq daf79c38bffd: P2 M Ground Theory Heights  Heights MCChart Gradient u eq daf79c38bffd
-- statement:
--   The P2 M Ground Theory Heights  Heights MCChart Gradient u eq daf79c38bffd construction uses the P2 M Ground Theory Heights  Heights MCChart Gradient u eq daf79c38bffd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartGradient.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartGradient.lean#L14-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartGradient
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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartGradient

theorem P2M_GroundTheory_Heights__Heights_MCChartGradient_u_eq_daf79c38bffd (D : PeriodChartData) :
    D.u = fun q => logDetGram (D.Y q.1) (D.f q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCChartGradient».«u_eq» := P2M_GroundTheory_Heights__Heights_MCChartGradient_u_eq_daf79c38bffd
