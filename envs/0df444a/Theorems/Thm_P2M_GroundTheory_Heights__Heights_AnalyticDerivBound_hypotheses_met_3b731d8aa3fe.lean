-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticDerivBound_hypotheses_met_3b731d8aa3fe
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticDerivBound_hypotheses_met_3b731d8aa3fe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:12.09186+00:00
-- url     : https://prove2.me/theorems/d3434dae-e437-418c-8aa8-e57cb65ef60a
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Deriv Bound hypotheses met 3b731d8aa3fe: P2 M Ground Theory Heights  Heights Analytic Deriv Bound hypotheses met 3b731d8aa3fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Deriv Bound hypotheses met 3b731d8aa3fe construction uses the P2 M Ground Theory Heights  Heights Analytic Deriv Bound hypotheses met 3b731d8aa3fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean#L105-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
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

theorem P2M_GroundTheory_Heights__Heights_AnalyticDerivBound_hypotheses_met_3b731d8aa3fe :
    IsOpen (Set.univ : Set ℂ) ∧ AnalyticOnNhd ℂ (fun x : ℂ => x) Set.univ ∧
      IsCompact (Metric.closedBall (0 : ℂ) 1) ∧ Metric.closedBall (0 : ℂ) 1 ⊆ Set.univ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticDerivBound».«hypotheses_met» := P2M_GroundTheory_Heights__Heights_AnalyticDerivBound_hypotheses_met_3b731d8aa3fe
