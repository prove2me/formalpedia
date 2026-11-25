-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_half_log_add_le_half_log_885b1995f26a
-- name    : P2M_GroundTheory_Heights__Heights_half_log_add_le_half_log_885b1995f26a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:35.91873+00:00
-- url     : https://prove2.me/theorems/0d355687-0ecb-4b00-a967-27028fed37b1
-- title:
--   P2 M Ground Theory Heights  Heights half log add le half log 885b1995f26a: P2 M Ground Theory Heights  Heights half log add le half log 885b1995f26a
-- statement:
--   The P2 M Ground Theory Heights  Heights half log add le half log 885b1995f26a construction uses the P2 M Ground Theory Heights  Heights half log add le half log 885b1995f26a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PConstants.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PConstants.lean#L51-L53

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

theorem P2M_GroundTheory_Heights__Heights_half_log_add_le_half_log_885b1995f26a (D ρ : ℝ) (hD : 1 ≤ D) (hρ : 2 ^ 26 ≤ ρ) :
    (1 / 2) * (log 280 + D * log (2 * π)) ≤ 3.8 * D ∧ 3.8 * D ≤ (D / 2) * log ρ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«half_log_add_le_half_log» := P2M_GroundTheory_Heights__Heights_half_log_add_le_half_log_885b1995f26a
