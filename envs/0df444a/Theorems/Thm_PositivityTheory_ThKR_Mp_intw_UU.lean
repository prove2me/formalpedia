-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_intw_UU
-- name    : PositivityTheory.ThKR.Mp.intw_UU
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:34.270166+00:00
-- url     : https://prove2.me/theorems/9e7d6fc6-b8d5-4ae3-b2ea-646ae6f36daf
-- title:
--   Mp: intw UU
-- statement:
--   The Mp construction uses the intw UU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L140-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L140-L146

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

theorem PositivityTheory.ThKR.Mp.intw_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (p q : Eu l) :
    Intw (UU S t) p q (p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q) q := by sorry
