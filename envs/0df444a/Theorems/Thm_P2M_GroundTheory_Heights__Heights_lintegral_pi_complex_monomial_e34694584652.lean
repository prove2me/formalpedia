-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_pi_complex_monomial_e34694584652
-- name    : P2M_GroundTheory_Heights__Heights_lintegral_pi_complex_monomial_e34694584652
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:05.661094+00:00
-- url     : https://prove2.me/theorems/117de3c7-b7d9-4cc5-b4ac-802029e0a6a3
-- title:
--   P2 M Ground Theory Heights  Heights lintegral pi complex monomial e34694584652: P2 M Ground Theory Heights  Heights lintegral pi complex monomial e34694584652
-- statement:
--   The P2 M Ground Theory Heights  Heights lintegral pi complex monomial e34694584652 construction uses the P2 M Ground Theory Heights  Heights lintegral pi complex monomial e34694584652 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FubiniStudyIntegral.lean#L168-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FubiniStudyIntegral.lean#L168-L241

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

theorem P2M_GroundTheory_Heights__Heights_lintegral_pi_complex_monomial_e34694584652 (k : ℕ) : ∀ (N : ℕ) (b : Fin N → ℕ) (c : ℝ), 0 < c →
    ∫⁻ z : Fin N → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) =
      ENNReal.ofReal (π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial /
        (∑ j, b j + N + k).factorial / c ^ (k + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«lintegral_pi_complex_monomial» := P2M_GroundTheory_Heights__Heights_lintegral_pi_complex_monomial_e34694584652
