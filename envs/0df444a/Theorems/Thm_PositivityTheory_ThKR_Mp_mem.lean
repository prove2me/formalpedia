-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_mem
-- name    : PositivityTheory.ThKR.Mp.mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:33.47066+00:00
-- url     : https://prove2.me/theorems/d90ce54b-0ccc-41fb-93b5-75433cd65980
-- title:
--   Mp: mem
-- statement:
--   The Mp construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L95-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L95-L95

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

theorem PositivityTheory.ThKR.Mp.mem (g : G l) : Mem (Subtype.val (p := (· ∈ sub l)) g) := by sorry
