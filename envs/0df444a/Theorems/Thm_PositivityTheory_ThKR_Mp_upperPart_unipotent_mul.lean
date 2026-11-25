-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_upperPart_unipotent_mul
-- name    : PositivityTheory.ThKR.Mp.upperPart_unipotent_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:08.662641+00:00
-- url     : https://prove2.me/theorems/8c6272f0-9ae3-5e82-9934-89f828dc2655
-- title:
--   Mp: upper Part unipotent mul
-- statement:
--   The Mp construction uses the upper Part unipotent mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L86-L98

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

theorem PositivityTheory.ThKR.Mp.upperPart_unipotent_mul (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) :
    upperParabolic (nn S t * s) = upperParabolic s + (t : ℂ) • (S.map ofReal * loQ s) := by sorry
