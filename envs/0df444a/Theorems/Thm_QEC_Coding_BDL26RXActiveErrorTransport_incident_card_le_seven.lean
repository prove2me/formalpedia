-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_incident_card_le_seven
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.incident_card_le_seven
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:48:10.10403+00:00
-- url     : https://prove2.me/theorems/ab58cc1a-429b-4d7a-9649-0fa0bc65aa97
-- title:
--   BDL26 RXActive Error Transport: incident card le seven
-- statement:
--   Seven is derived from the recursively instantiated actual Tanner degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L269-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L269-L271

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.incident_card_le_seven (x : XCoord S i) : (incidentQ S depth i x).card ≤ 7 := by sorry
