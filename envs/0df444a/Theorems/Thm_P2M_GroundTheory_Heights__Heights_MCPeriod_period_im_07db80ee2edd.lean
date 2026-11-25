-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPeriod_period_im_07db80ee2edd
-- name    : P2M_GroundTheory_Heights__Heights_MCPeriod_period_im_07db80ee2edd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:39.367556+00:00
-- url     : https://prove2.me/theorems/4dc6694d-6334-4e24-96eb-2fcf563614b3
-- title:
--   P2 M Ground Theory Heights  Heights MCPeriod period im 07db80ee2edd: P2 M Ground Theory Heights  Heights MCPeriod period im 07db80ee2edd
-- statement:
--   The P2 M Ground Theory Heights  Heights MCPeriod period im 07db80ee2edd construction uses the P2 M Ground Theory Heights  Heights MCPeriod period im 07db80ee2edd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Period.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Period.lean#L22-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Period
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPeriod
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCPeriod_period_im_07db80ee2edd (D : PeriodChartData) (z : Fin D.n → ℂ) (l : Fin D.a → ℂ)
    (h : ∀ j, Complex.exp (l j) = cuspCoord D.a_le z j) :
    (D.period z l).map Complex.im = D.Y z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCPeriod».«period_im» := P2M_GroundTheory_Heights__Heights_MCPeriod_period_im_07db80ee2edd
