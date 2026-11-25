-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_qd_sum
-- name    : PositivityTheory.ThKR.Mp.qd_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:14.765004+00:00
-- url     : https://prove2.me/theorems/218d6095-6b40-5b2f-8f5e-b19972abd1de
-- title:
--   Mp: qd sum
-- statement:
--   The Mp construction uses the qd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MpFOne.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MpFOne.lean#L45-L52

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
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
open scoped Real ContDiff RealInnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.Mp.qd_sum (X : Mat l) (f : Sch l) : ∑ a, ∑ b, X a b • Qd (Matrix.single a b 1) f = Qd X f := by sorry
