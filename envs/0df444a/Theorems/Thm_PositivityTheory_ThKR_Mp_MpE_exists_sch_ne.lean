-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_MpE_exists_sch_ne
-- name    : PositivityTheory.ThKR.Mp.MpE.exists_sch_ne
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:08.894599+00:00
-- url     : https://prove2.me/theorems/a944e5de-0eed-5760-80e2-bcd3e454dc2f
-- title:
--   Mp E: exists sch ne
-- statement:
--   The Mp E construction uses the exists sch ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticGroupT2Space.lean#L56-L62

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
open PositivityTheory.ThKR.Mp.MpE

theorem PositivityTheory.ThKR.Mp.MpE.exists_sch_ne : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by sorry
