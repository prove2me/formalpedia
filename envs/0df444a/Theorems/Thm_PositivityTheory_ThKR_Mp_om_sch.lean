-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_om_sch
-- name    : PositivityTheory.ThKR.Mp.om_sch
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:22:49.310886+00:00
-- url     : https://prove2.me/theorems/7cbcfa82-3f2c-5648-8413-36af4f480090
-- title:
--   Mp: om sch
-- statement:
--   The Mp construction uses the om sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L97-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L97-L97

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
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
variable (l : Type) [Fintype l] [DecidableEq l]
variable {l}

theorem PositivityTheory.ThKR.Mp.om_sch (g : G l) (f : Sch l) : om g (schwartzToL2 l f) = schwartzToL2 l (omS g f) := by sorry
