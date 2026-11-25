-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_J_mul_transpose_inr
-- name    : PositivityTheory.ThKR.Mp.J_mul_transpose_inr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:30:27.117199+00:00
-- url     : https://prove2.me/theorems/d7d0e4bd-f5df-4dc3-953b-6ffe769ac049
-- title:
--   Mp: J mul transpose inr
-- statement:
--   The Mp construction uses the J mul transpose inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L16-L18

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

theorem PositivityTheory.ThKR.Mp.J_mul_transpose_inr (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inr a) j = s j (.inl a) := by sorry
