-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_q_constant
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.remainder_q_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:54:36.648198+00:00
-- url     : https://prove2.me/theorems/ad80d200-f9d2-409e-9b77-42c685db2ae2
-- title:
--   BDL26 RXFinite Block Transport: remainder q constant
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the remainder q constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L405-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L405-L409

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_q_constant

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.remainder_q_constant (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    R S depth i h X0 a b (rxQVertexEquiv S depth i h q v).val = L S depth i h X0 a b q := by sorry
