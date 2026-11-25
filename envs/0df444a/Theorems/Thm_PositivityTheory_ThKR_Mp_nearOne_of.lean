-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_nearOne_of
-- name    : PositivityTheory.ThKR.Mp.nearOne_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:29:49.321448+00:00
-- url     : https://prove2.me/theorems/6449c1f6-d72d-431c-adae-b1e71ee5c2e0
-- title:
--   Mp: near One of
-- statement:
--   The Mp construction uses the near One of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean#L68-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean#L68-L103

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open MpE

theorem PositivityTheory.ThKR.Mp.nearOne_of (hS : SecEx l) (hK : Ker l) (hD : SecDer l) : NearOne l := by sorry
