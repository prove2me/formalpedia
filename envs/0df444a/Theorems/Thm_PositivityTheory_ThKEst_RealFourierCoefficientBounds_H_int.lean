-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_int
-- name    : PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:30.921513+00:00
-- url     : https://prove2.me/theorems/9a1c9351-37a3-4671-b67e-b76c9899b11e
-- title:
--   Real Fourier Coefficient Bounds: H int
-- statement:
--   The Real Fourier Coefficient Bounds construction uses the H int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L84-L109

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

theorem PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_int (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x : V) (j : ℕ), j ≤ N →
    Integrable (fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) ∧
    (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by sorry
