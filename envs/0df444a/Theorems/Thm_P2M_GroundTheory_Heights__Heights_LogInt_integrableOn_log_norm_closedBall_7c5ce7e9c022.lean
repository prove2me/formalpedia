-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_closedBall_7c5ce7e9c022
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_closedBall_7c5ce7e9c022
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:13.425825+00:00
-- url     : https://prove2.me/theorems/2a7ebc5d-615a-4bfb-afc0-1b3980395e78
-- title:
--   P2 M Ground Theory Heights  Heights Log Int integrable On log norm closed Ball 7c5ce7e9c022: P2 M Ground Theory Heights  Heights Log Int integrable On log norm closed Ball 7c5ce7e9c022
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int integrable On log norm closed Ball 7c5ce7e9c022 construction uses the P2 M Ground Theory Heights  Heights Log Int integrable On log norm closed Ball 7c5ce7e9c022 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L115-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L115-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_closedBall_7c5ce7e9c022 (r : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.closedBall 0 r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«integrableOn_log_norm_closedBall» := P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_closedBall_7c5ce7e9c022
