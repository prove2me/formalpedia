-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_level_b7e577dac56b
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_level_b7e577dac56b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:11.110817+00:00
-- url     : https://prove2.me/theorems/930e1eb2-198d-565d-878c-3fb8d5123a9d
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS lift level b7e577dac56b: P2 M Ground Theory Heights  Heights Effective HS lift level b7e577dac56b
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS lift level b7e577dac56b construction uses the P2 M Ground Theory Heights  Heights Effective HS lift level b7e577dac56b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L196-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L196-L197

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_level_b7e577dac56b (D T a : ℕ) (hD : 1 ≤ D) (ha : a + D + 1 ≤ T) :
    D + 1 ≤ T - a ∧ 2 ≤ D + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«lift_level» := P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_level_b7e577dac56b
