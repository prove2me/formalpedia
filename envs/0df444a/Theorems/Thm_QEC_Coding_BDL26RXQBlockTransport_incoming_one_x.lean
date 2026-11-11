-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incoming_one_x
-- name    : QEC.Coding.BDL26RXQBlockTransport.incoming_one_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:31:43.709828+00:00
-- url     : https://prove2.me/theorems/397ebe27-7529-4fa6-97e1-e96929898c18
-- title:
--   BDL26 RXQBlock Transport: incoming one x
-- statement:
--   The original Tanner orientation has no incoming edge at an X centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L79-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L79-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.incoming_one_x (x : XCoord S i)
    (v : RXVertex (XCoord S i) (QCoord S i) (ZCoord S i))
    (hv : (Data S depth i h).levelGraph.graph.distance v (.inl x) ≤ 1) :
    v = .inl x := by sorry
