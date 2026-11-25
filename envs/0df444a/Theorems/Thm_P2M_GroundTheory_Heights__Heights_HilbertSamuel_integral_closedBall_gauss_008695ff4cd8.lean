-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_integral_closedBall_gauss_008695ff4cd8
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_integral_closedBall_gauss_008695ff4cd8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:55.13581+00:00
-- url     : https://prove2.me/theorems/8ca992f7-5d9d-4d7a-b960-607bdee6b80f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel integral closed Ball gauss 008695ff4cd8: P2 M Ground Theory Heights  Heights Hilbert Samuel integral closed Ball gauss 008695ff4cd8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel integral closed Ball gauss 008695ff4cd8 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel integral closed Ball gauss 008695ff4cd8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L142-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L142-L183

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_integral_closedBall_gauss_008695ff4cd8 (c ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫ z in closedBall (0 : ℂ) ρ, Real.exp (-c * ‖z‖ ^ 2) =
      if c = 0 then π * ρ ^ 2 else π * (1 - Real.exp (-c * ρ ^ 2)) / c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«integral_closedBall_gauss» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_integral_closedBall_gauss_008695ff4cd8
