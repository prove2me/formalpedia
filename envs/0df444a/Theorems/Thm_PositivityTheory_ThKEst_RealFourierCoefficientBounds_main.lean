-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_main
-- name    : PositivityTheory.ThKEst.RealFourierCoefficientBounds.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:49.643964+00:00
-- url     : https://prove2.me/theorems/133a2051-003e-4353-a17d-3fef8c5bf6a1
-- title:
--   Real Fourier Coefficient Bounds: main
-- statement:
--   The Real Fourier Coefficient Bounds construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L159-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L159-L179

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

theorem PositivityTheory.ThKEst.RealFourierCoefficientBounds.main (N : ℕ) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x y : V),
    ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)‖ *
      (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by sorry
