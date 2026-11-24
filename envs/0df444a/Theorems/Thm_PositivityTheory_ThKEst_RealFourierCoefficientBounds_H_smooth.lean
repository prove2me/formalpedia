-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_smooth
-- name    : PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:59.482911+00:00
-- url     : https://prove2.me/theorems/85e08b50-be1a-416f-a78e-d3f1b67ffc16
-- title:
--   Real Fourier Coefficient Bounds: H smooth
-- statement:
--   The Real Fourier Coefficient Bounds construction uses the H smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L28-L29

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

theorem PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_smooth (f₁ f₂ : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ (H f₁ f₂ x) := by sorry
