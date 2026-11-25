-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_sq_norm_mul_setIntegral_le_c926ed7b3320
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_sq_norm_mul_setIntegral_le_c926ed7b3320
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:49.86151+00:00
-- url     : https://prove2.me/theorems/64b721f5-43ad-5720-83a5-1a9883cd975f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel sq norm mul set Integral le c926ed7b3320: P2 M Ground Theory Heights  Heights Hilbert Samuel sq norm mul set Integral le c926ed7b3320
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel sq norm mul set Integral le c926ed7b3320 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel sq norm mul set Integral le c926ed7b3320 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L103-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L103-L140

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_sq_norm_mul_setIntegral_le_c926ed7b3320 {D : ℕ} {ρ : ℝ} {g : (Fin D → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ)) {w : (Fin D → ℂ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ z, 0 ≤ w z) (hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z) :
    ‖g 0‖ ^ 2 * ∫ z in closedBall (0 : Fin D → ℂ) ρ, w z ≤
      ∫ z in closedBall (0 : Fin D → ℂ) ρ, ‖g z‖ ^ 2 * w z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«sq_norm_mul_setIntegral_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_sq_norm_mul_setIntegral_le_c926ed7b3320
