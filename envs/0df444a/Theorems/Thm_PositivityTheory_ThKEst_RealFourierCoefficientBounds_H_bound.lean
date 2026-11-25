-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_bound
-- name    : PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:14.272292+00:00
-- url     : https://prove2.me/theorems/0ce4e6db-abc2-5b9d-97b3-f3499e3ff403
-- title:
--   Real Fourier Coefficient Bounds: H bound
-- statement:
--   The Real Fourier Coefficient Bounds construction uses the H bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L36-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L36-L73

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.RealFourierCoefficientBounds
open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_bound (N D : ℕ) (f₁ f₂ : SchwartzMap V ℂ) (x u : V) {j : ℕ} (hj : j ≤ N) :
    (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) := by sorry
