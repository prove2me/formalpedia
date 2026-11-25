-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_pi_complex_monomial_a6e17cc41656
-- name    : P2M_GroundTheory_Heights__Heights_integral_pi_complex_monomial_a6e17cc41656
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:40:48.613835+00:00
-- url     : https://prove2.me/theorems/82a3620c-b71b-5dc3-a19f-fab2a7e59268
-- title:
--   P2 M Ground Theory Heights  Heights integral pi complex monomial a6e17cc41656: P2 M Ground Theory Heights  Heights integral pi complex monomial a6e17cc41656
-- statement:
--   The P2 M Ground Theory Heights  Heights integral pi complex monomial a6e17cc41656 construction uses the P2 M Ground Theory Heights  Heights integral pi complex monomial a6e17cc41656 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FubiniStudyIntegral.lean#L243-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FubiniStudyIntegral.lean#L243-L258

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

theorem P2M_GroundTheory_Heights__Heights_integral_pi_complex_monomial_a6e17cc41656 (k N : ℕ) (b : Fin N → ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) ∧
    ∫ z : Fin N → ℂ, (∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) =
      π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial / (∑ j, b j + N + k).factorial /
        c ^ (k + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_pi_complex_monomial» := P2M_GroundTheory_Heights__Heights_integral_pi_complex_monomial_a6e17cc41656
