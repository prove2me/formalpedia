-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_q_cont
-- name    : PositivityTheory.ThKEst.RealFourierCoefficientBounds.q_cont
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:44.585914+00:00
-- url     : https://prove2.me/theorems/2d4691ff-79ff-4ffc-81e9-e2c5f45a088c
-- title:
--   Real Fourier Coefficient Bounds: q cont
-- statement:
--   The Real Fourier Coefficient Bounds construction uses the q cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefRealA.lean#L15-L18

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

theorem PositivityTheory.ThKEst.RealFourierCoefficientBounds.q_cont (M N : ℕ) : Continuous (q V M N) := by sorry
