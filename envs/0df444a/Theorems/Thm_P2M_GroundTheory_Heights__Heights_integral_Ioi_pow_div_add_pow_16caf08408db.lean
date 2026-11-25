-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_Ioi_pow_div_add_pow_16caf08408db
-- name    : P2M_GroundTheory_Heights__Heights_integral_Ioi_pow_div_add_pow_16caf08408db
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:59.972797+00:00
-- url     : https://prove2.me/theorems/d7a40594-52a7-4f09-8a9c-2ef887a11375
-- title:
--   P2 M Ground Theory Heights  Heights integral Ioi pow div add pow 16caf08408db: P2 M Ground Theory Heights  Heights integral Ioi pow div add pow 16caf08408db
-- statement:
--   The P2 M Ground Theory Heights  Heights integral Ioi pow div add pow 16caf08408db construction uses the P2 M Ground Theory Heights  Heights integral Ioi pow div add pow 16caf08408db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FubiniStudyIntegral.lean#L8-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FubiniStudyIntegral.lean#L8-L127

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FubiniStudyIntegral
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
open MeasureTheory Set Filter Topology Real

theorem P2M_GroundTheory_Heights__Heights_integral_Ioi_pow_div_add_pow_16caf08408db (c : ℝ) (hc : 0 < c) (k : ℕ) : ∀ b : ℕ,
    IntegrableOn (fun t : ℝ => t ^ b / (c + t) ^ (b + 2 + k)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), t ^ b / (c + t) ^ (b + 2 + k) =
      ((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_Ioi_pow_div_add_pow» := P2M_GroundTheory_Heights__Heights_integral_Ioi_pow_div_add_pow_16caf08408db
