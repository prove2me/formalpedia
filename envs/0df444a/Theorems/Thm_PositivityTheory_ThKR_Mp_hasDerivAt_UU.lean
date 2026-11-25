-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_hasDerivAt_UU
-- name    : PositivityTheory.ThKR.Mp.hasDerivAt_UU
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:26.895976+00:00
-- url     : https://prove2.me/theorems/34b67917-8f7d-4f1b-a8d8-b55d745de043
-- title:
--   Mp: has Deriv At UU
-- statement:
--   The Mp construction uses the has Deriv At UU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L173-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L173-L228

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.Mp.hasDerivAt_UU (S : Matrix l l ℝ) (f : Sch l) (t₀ : ℝ) :
    HasDerivAt (fun t => UU S t f 0)
      (fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l (UU S t₀ f))) 0) t₀ := by sorry
