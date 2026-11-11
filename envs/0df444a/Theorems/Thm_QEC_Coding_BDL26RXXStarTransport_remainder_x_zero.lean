-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_x_zero
-- name    : QEC.Coding.BDL26RXXStarTransport.remainder_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:59:41.087284+00:00
-- url     : https://prove2.me/theorems/b7bb6026-646f-4e10-84f0-0efc481ae256
-- title:
--   BDL26 RXXStar Transport: remainder x zero
-- statement:
--   This zero-X ERROR statement is established before any staged Q argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L226-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L226-L234

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

theorem QEC.Coding.BDL26RXXStarTransport.remainder_x_zero (x y : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (remainder S depth i h x a b)=0 := by sorry
