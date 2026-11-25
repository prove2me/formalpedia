-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_coord_5e7af9876972
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_coord_5e7af9876972
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:25.671671+00:00
-- url     : https://prove2.me/theorems/96628855-309f-4f11-a8c2-15a811a4d0f5
-- title:
--   P2 M Ground Theory Heights  Heights Log Int integrable On log norm coord 5e7af9876972: P2 M Ground Theory Heights  Heights Log Int integrable On log norm coord 5e7af9876972
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int integrable On log norm coord 5e7af9876972 construction uses the P2 M Ground Theory Heights  Heights Log Int integrable On log norm coord 5e7af9876972 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L132-L138

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_coord_5e7af9876972 [Fintype ι] (r : ℝ) (x : ι) :
    IntegrableOn (fun u : ι → ℂ => Real.log ‖u x‖) (polydisc ι r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«integrableOn_log_norm_coord» := P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_norm_coord_5e7af9876972
