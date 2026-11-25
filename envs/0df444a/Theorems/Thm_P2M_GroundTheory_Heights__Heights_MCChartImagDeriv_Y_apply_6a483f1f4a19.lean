-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartImagDeriv_Y_apply_6a483f1f4a19
-- name    : P2M_GroundTheory_Heights__Heights_MCChartImagDeriv_Y_apply_6a483f1f4a19
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:45:26.376275+00:00
-- url     : https://prove2.me/theorems/9fc54500-db6b-57ba-9e40-ece690dd04d9
-- title:
--   P2 M Ground Theory Heights  Heights MCChart Imag Deriv Y apply 6a483f1f4a19: P2 M Ground Theory Heights  Heights MCChart Imag Deriv Y apply 6a483f1f4a19
-- statement:
--   The P2 M Ground Theory Heights  Heights MCChart Imag Deriv Y apply 6a483f1f4a19 construction uses the P2 M Ground Theory Heights  Heights MCChart Imag Deriv Y apply 6a483f1f4a19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartImagDeriv.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartImagDeriv.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagDeriv
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
open GroundTheory.Heights₂.Heights.MCChartImagDeriv

theorem P2M_GroundTheory_Heights__Heights_MCChartImagDeriv_Y_apply_6a483f1f4a19 (D : PeriodChartData) (z : Fin D.n → ℂ) (j l : Fin D.g) :
    D.Y z j l = (D.τ0 z j l).im + ∑ i, cuspTime D.a_le z i * D.B i j l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCChartImagDeriv».«Y_apply» := P2M_GroundTheory_Heights__Heights_MCChartImagDeriv_Y_apply_6a483f1f4a19
