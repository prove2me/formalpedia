-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_fourier_bound
-- name    : PositivityTheory.ThKEst.RealFourierCoefficientBounds.fourier_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:37.2685+00:00
-- url     : https://prove2.me/theorems/3062e71e-4038-4e93-9686-83ab77432e39
-- title:
--   Real Fourier Coefficient Bounds: fourier bound
-- statement:
--   The Real Fourier Coefficient Bounds construction uses the fourier bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L111-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L111-L157

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
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem PositivityTheory.ThKEst.RealFourierCoefficientBounds.fourier_bound (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x w : V),
    ‖𝓕 (H f₁ f₂ x) w‖ * (1 + ‖x‖ + ‖w‖) ^ N ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by sorry
