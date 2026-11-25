-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pow_two_mul_sub_one_le_dcc969861cb5
-- name    : P2M_GroundTheory_Heights__Heights_pow_two_mul_sub_one_le_dcc969861cb5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:16.729726+00:00
-- url     : https://prove2.me/theorems/1a9e27e5-dc81-4309-87ba-e593380e982d
-- title:
--   P2 M Ground Theory Heights  Heights pow two mul sub one le dcc969861cb5: P2 M Ground Theory Heights  Heights pow two mul sub one le dcc969861cb5
-- statement:
--   The P2 M Ground Theory Heights  Heights pow two mul sub one le dcc969861cb5 construction uses the P2 M Ground Theory Heights  Heights pow two mul sub one le dcc969861cb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L55-L60

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

theorem P2M_GroundTheory_Heights__Heights_pow_two_mul_sub_one_le_dcc969861cb5 {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : r ^ (2 * m - 1) ≤ (1 + r ^ 2) ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pow_two_mul_sub_one_le» := P2M_GroundTheory_Heights__Heights_pow_two_mul_sub_one_le_dcc969861cb5
