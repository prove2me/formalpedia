-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_cuspTime_continuousOn_ff6645c3856f
-- name    : P2M_GroundTheory_Heights__Heights_cuspTime_continuousOn_ff6645c3856f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:24.464085+00:00
-- url     : https://prove2.me/theorems/38e0bb78-b132-5ca4-916c-9a1418bc980c
-- title:
--   P2 M Ground Theory Heights  Heights cusp Time continuous On ff6645c3856f: P2 M Ground Theory Heights  Heights cusp Time continuous On ff6645c3856f
-- statement:
--   The P2 M Ground Theory Heights  Heights cusp Time continuous On ff6645c3856f construction uses the P2 M Ground Theory Heights  Heights cusp Time continuous On ff6645c3856f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartImagContinuous.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartImagContinuous.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagContinuous
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

theorem P2M_GroundTheory_Heights__Heights_cuspTime_continuousOn_ff6645c3856f {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) (j : Fin a) :
    ContinuousOn (fun z => cuspTime h z j) (puncturedChart h U) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«cuspTime_continuousOn» := P2M_GroundTheory_Heights__Heights_cuspTime_continuousOn_ff6645c3856f
