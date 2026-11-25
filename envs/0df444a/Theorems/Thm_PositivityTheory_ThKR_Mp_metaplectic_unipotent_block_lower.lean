-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_metaplectic_unipotent_block_lower
-- name    : PositivityTheory.ThKR.Mp.metaplectic_unipotent_block_lower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:32.667207+00:00
-- url     : https://prove2.me/theorems/23299b92-cf78-5c07-aac8-d9a8b4d135f6
-- title:
--   Mp: metaplectic unipotent block lower
-- statement:
--   The Mp construction uses the metaplectic unipotent block lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L116-L118

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

theorem PositivityTheory.ThKR.Mp.metaplectic_unipotent_block_lower (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inr Sum.inl (nn S t) = 0 := by sorry
