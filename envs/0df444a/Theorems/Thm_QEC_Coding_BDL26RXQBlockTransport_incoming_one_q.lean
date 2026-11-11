-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incoming_one_q
-- name    : QEC.Coding.BDL26RXQBlockTransport.incoming_one_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:36:58.161369+00:00
-- url     : https://prove2.me/theorems/d1785533-65da-49da-9ad5-ef7f1f754260
-- title:
--   BDL26 RXQBlock Transport: incoming one q
-- statement:
--   Incoming radius one at Q consists of that Q and its incident X vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L89-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L89-L100

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

theorem QEC.Coding.BDL26RXQBlockTransport.incoming_one_q (q : QCoord S i)
    (v : RXVertex (XCoord S i) (QCoord S i) (ZCoord S i))
    (hv : (Data S depth i h).levelGraph.graph.distance v (.inr (.inl q)) ≤ 1) :
    v = .inr (.inl q) ∨
      ∃ x, v = .inl x ∧ (state S i.val).presentation.xq x q = true := by sorry
