-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_q_kernel
-- name    : QEC.Coding.BDL26RXXStarTransport.remainder_q_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:11:05.836212+00:00
-- url     : https://prove2.me/theorems/49119272-eb5e-40df-8797-9124e20ea3c3
-- title:
--   BDL26 RXXStar Transport: remainder q kernel
-- statement:
--   Now the original staged Cq formula applies, with zero X errors proved above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L255-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L255-L262

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

theorem QEC.Coding.BDL26RXXStarTransport.remainder_q_kernel (x : XCoord S i) (q : QCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    (rxContract S depth i h).rx_local_complexes.cqDelta1 q
      (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (remainder S depth i h x a b))=0 := by sorry
