-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_incident_card_eq_tannerDegree
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.incident_card_eq_tannerDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:43:48.531985+00:00
-- url     : https://prove2.me/theorems/53c3f5bd-d007-499c-91b1-974ad4e143ce
-- title:
--   BDL26 RXActive Error Transport: incident card eq tanner Degree
-- statement:
--   The BDL26 RXActive Error Transport construction uses the incident card eq tanner Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L263-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L263-L266

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.incident_card_eq_tannerDegree (x : XCoord S i) :
    (incidentQ S depth i x).card=tannerDegree (state S i.val).presentation (.x x) := by sorry
