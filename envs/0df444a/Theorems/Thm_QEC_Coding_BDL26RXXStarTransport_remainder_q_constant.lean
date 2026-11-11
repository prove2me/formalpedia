-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_q_constant
-- name    : QEC.Coding.BDL26RXXStarTransport.remainder_q_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:05:36.909408+00:00
-- url     : https://prove2.me/theorems/3eae6bf0-7db5-4dd4-873b-3691c8598e09
-- title:
--   BDL26 RXXStar Transport: remainder q constant
-- statement:
--   The BDL26 RXXStar Transport construction uses the remainder q constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L269-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L269-L274

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.remainder_q_constant (x : XCoord S i) (q : QCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    remainder S depth i h x a b (rxQVertexEquiv S depth i h q v).val =
      lowerWord S depth i h x a b q := by sorry
