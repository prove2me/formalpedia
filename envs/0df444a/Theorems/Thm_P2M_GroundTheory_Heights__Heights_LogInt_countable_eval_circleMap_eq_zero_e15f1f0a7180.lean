-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_countable_eval_circleMap_eq_zero_e15f1f0a7180
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_countable_eval_circleMap_eq_zero_e15f1f0a7180
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:55.22713+00:00
-- url     : https://prove2.me/theorems/dc673b53-a61d-4a0d-b382-f463e3d14eef
-- title:
--   P2 M Ground Theory Heights  Heights Log Int countable eval circle Map eq zero e15f1f0a7180: P2 M Ground Theory Heights  Heights Log Int countable eval circle Map eq zero e15f1f0a7180
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int countable eval circle Map eq zero e15f1f0a7180 construction uses the P2 M Ground Theory Heights  Heights Log Int countable eval circle Map eq zero e15f1f0a7180 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntCircle.lean#L88-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt

theorem P2M_GroundTheory_Heights__Heights_LogInt_countable_eval_circleMap_eq_zero_e15f1f0a7180 (P : Polynomial ℂ) (hP : P ≠ 0) :
    {θ : ℝ | P.eval (circleMap 0 1 θ) = 0}.Countable := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«countable_eval_circleMap_eq_zero» := P2M_GroundTheory_Heights__Heights_LogInt_countable_eval_circleMap_eq_zero_e15f1f0a7180
