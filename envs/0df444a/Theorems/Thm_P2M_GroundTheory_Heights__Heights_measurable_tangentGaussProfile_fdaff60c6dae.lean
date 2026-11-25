-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tangentGaussProfile_fdaff60c6dae
-- name    : P2M_GroundTheory_Heights__Heights_measurable_tangentGaussProfile_fdaff60c6dae
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:47.947956+00:00
-- url     : https://prove2.me/theorems/68a4ba0c-e829-5329-a895-2c32c8f58237
-- title:
--   P2 M Ground Theory Heights  Heights measurable tangent Gauss Profile fdaff60c6dae: P2 M Ground Theory Heights  Heights measurable tangent Gauss Profile fdaff60c6dae
-- statement:
--   The P2 M Ground Theory Heights  Heights measurable tangent Gauss Profile fdaff60c6dae construction uses the P2 M Ground Theory Heights  Heights measurable tangent Gauss Profile fdaff60c6dae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L45-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_measurable_tangentGaussProfile_fdaff60c6dae (n m : ℕ) : Measurable (tangentGaussProfile n m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurable_tangentGaussProfile» := P2M_GroundTheory_Heights__Heights_measurable_tangentGaussProfile_fdaff60c6dae
