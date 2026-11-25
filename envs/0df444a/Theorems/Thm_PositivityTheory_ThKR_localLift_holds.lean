-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_localLift_holds
-- name    : PositivityTheory.ThKR.localLift_holds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:52.051097+00:00
-- url     : https://prove2.me/theorems/1ceea49b-7986-4dbc-ad37-821102568ec4
-- title:
--   Th KR: local Lift holds
-- statement:
--   The Th KR construction uses the local Lift holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L153-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L153-L228

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR
open LL

theorem PositivityTheory.ThKR.localLift_holds : LocalLift := by sorry
