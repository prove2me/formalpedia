-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_smooth_of
-- name    : PositivityTheory.ThKR.Mp.smooth_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:50.944224+00:00
-- url     : https://prove2.me/theorems/1c348e42-0443-5e9d-b5af-7adc57d9fac4
-- title:
--   Mp: smooth of
-- statement:
--   The Mp construction uses the smooth of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOrb.lean#L87-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOrb.lean#L87-L104

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOrb
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

theorem PositivityTheory.ThKR.Mp.smooth_of (hT : TopG l) (hN : NearOne l) (hD : SecDer l) : Smooth l := by sorry
