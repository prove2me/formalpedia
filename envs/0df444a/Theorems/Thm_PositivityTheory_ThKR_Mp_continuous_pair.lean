-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_continuous_pair
-- name    : PositivityTheory.ThKR.Mp.continuous_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:49.071719+00:00
-- url     : https://prove2.me/theorems/e7cb3b4e-2946-56a2-8674-33b176b1311c
-- title:
--   Mp: continuous pair
-- statement:
--   The Mp construction uses the continuous pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L109-L110

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

theorem PositivityTheory.ThKR.Mp.continuous_pair : Continuous fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)) := by sorry
