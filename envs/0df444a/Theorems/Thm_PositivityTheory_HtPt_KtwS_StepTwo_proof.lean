-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_KtwS_StepTwo_proof
-- name    : PositivityTheory.HtPt.KtwS.StepTwo.proof
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:10:49.193479+00:00
-- url     : https://prove2.me/theorems/1852392c-b530-57bd-bb1f-c5434992deae
-- title:
--   Step Two: proof
-- statement:
--   The Step Two construction uses the proof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/ExistsLineBundleTwistMulOf.lean#L169-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/ExistsLineBundleTwistMulOf.lean#L169-L199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial
noncomputable section
universe u v w

theorem PositivityTheory.HtPt.KtwS.StepTwo.proof (hRed : StepTwo.Reduce.Statement.{u, v, w}) (hLT : LineTwist.Statement.{u, w})
    (hTA : TwistAlg.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hNR : NefRestrict.Statement.{u, w}) (hJP : StepData.JProper.Statement.{u, w})
    (hDrop : SubvarDrop.Statement.{u, w}) (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w}) :
    StepTwo.Statement.{u, v, w} := by sorry
