-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_hess
-- name    : PositivityTheory.ThKR.Mp.hess
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:28.339943+00:00
-- url     : https://prove2.me/theorems/7b82670e-139e-4ef8-bf5a-f95dd736065e
-- title:
--   Mp: hess
-- statement:
--   The Mp construction uses the hess property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L235-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L235-L254

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

theorem PositivityTheory.ThKR.Mp.hess {s : Mat l} {H : Sch l} (hA : Ann s H) (j k : l) :
    ∑ a, upperParabolic s a j * (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)} H)) 0 =
      -(2 * π * I) * loQ s k j * H 0 := by sorry
