-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_canonical_cx_eq
-- name    : QEC.Coding.BDL26RXXStarTransport.gradient_canonical_cx_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:20:12.486219+00:00
-- url     : https://prove2.me/theorems/7ed4f9dc-f01e-4d56-bb79-c23370d07fab
-- title:
--   BDL26 RXXStar Transport: gradient canonical cx eq
-- statement:
--   The actual canonical Cx outputs agree on the gradient perturbation, even with arbitrary background.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L468-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L468-L472

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

theorem QEC.Coding.BDL26RXXStarTransport.gradient_canonical_cx_eq (x y : XCoord S i) (a : Upper S depth i) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h)
        (errorSyndrome S depth i (a+gradientError S depth i h x)).val y := by sorry
