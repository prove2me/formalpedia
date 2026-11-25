-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_mul_weight_eq_d36808fe1b39
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_mul_weight_eq_d36808fe1b39
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:17.325905+00:00
-- url     : https://prove2.me/theorems/e5045689-2ab5-4e2e-89e6-4b9389c435a4
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral mul weight eq d36808fe1b39: P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral mul weight eq d36808fe1b39
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral mul weight eq d36808fe1b39 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel set Integral mul weight eq d36808fe1b39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L29-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PolydiscMean.lean#L29-L101

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_mul_weight_eq_d36808fe1b39 {D : ℕ} {ρ : ℝ} {g : (Fin D → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ)) {w : (Fin D → ℂ) → ℝ} (hw : Continuous w)
    (hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z) :
    ∫ z in closedBall (0 : Fin D → ℂ) ρ, g z * (w z : ℂ) =
      g 0 * ∫ z in closedBall (0 : Fin D → ℂ) ρ, (w z : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«setIntegral_mul_weight_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_mul_weight_eq_d36808fe1b39
