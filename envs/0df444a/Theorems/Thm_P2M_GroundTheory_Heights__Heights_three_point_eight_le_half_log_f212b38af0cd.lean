-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_three_point_eight_le_half_log_f212b38af0cd
-- name    : P2M_GroundTheory_Heights__Heights_three_point_eight_le_half_log_f212b38af0cd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:22.319839+00:00
-- url     : https://prove2.me/theorems/cbed1277-a60b-50d7-9be1-6e889c5be401
-- title:
--   P2 M Ground Theory Heights  Heights three point eight le half log f212b38af0cd: P2 M Ground Theory Heights  Heights three point eight le half log f212b38af0cd
-- statement:
--   The P2 M Ground Theory Heights  Heights three point eight le half log f212b38af0cd construction uses the P2 M Ground Theory Heights  Heights three point eight le half log f212b38af0cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PConstants.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PConstants.lean#L46-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
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
open Real

theorem P2M_GroundTheory_Heights__Heights_three_point_eight_le_half_log_f212b38af0cd (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    3.8 * D ≤ (D / 2) * log ρ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«three_point_eight_le_half_log» := P2M_GroundTheory_Heights__Heights_three_point_eight_le_half_log_f212b38af0cd
