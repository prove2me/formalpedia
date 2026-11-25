-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_isInducing_F
-- name    : PositivityTheory.ThKR.Mp.MpE.isInducing_F
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:46.366378+00:00
-- url     : https://prove2.me/theorems/4e0f9d5c-678f-544c-8321-347dd4b0bfcf
-- title:
--   Mp E: is Inducing F
-- statement:
--   The Mp E construction uses the is Inducing F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean#L107-L108

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
open PositivityTheory.ThKR.Mp.MpE

theorem PositivityTheory.ThKR.Mp.MpE.isInducing_F :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := by sorry
