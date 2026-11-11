-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder
-- name    : QEC.Coding.BDL26RXXStarTransport.map1_eq_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:02:40.29919+00:00
-- url     : https://prove2.me/theorems/bf23ca01-824e-4302-8bef-42e13f8b914e
-- title:
--   BDL26 RXXStar Transport: map1 eq remainder
-- statement:
--   Full selected map1, not only its restriction to the Q sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L292-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L292-L327

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

theorem QEC.Coding.BDL26RXXStarTransport.map1_eq_remainder (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
      remainder S depth i h x a b := by sorry
