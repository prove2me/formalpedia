-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_incident_card_eq_xDegree
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.incident_card_eq_xDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:39:31.323846+00:00
-- url     : https://prove2.me/theorems/7a055d65-93a7-434f-93cb-fcef001ee7b0
-- title:
--   BDL26 RXActive Error Transport: incident card eq x Degree
-- statement:
--   The BDL26 RXActive Error Transport construction uses the incident card eq x Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L259-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L259-L261

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXActiveErrorTransport.incident_card_eq_xDegree (x : XCoord S i) :
    (incidentQ S depth i x).card=xDegree (state S i.val).presentation x := by sorry
