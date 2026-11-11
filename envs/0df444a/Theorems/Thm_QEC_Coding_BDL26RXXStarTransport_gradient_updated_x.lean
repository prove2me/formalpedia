-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_updated_x
-- name    : QEC.Coding.BDL26RXXStarTransport.gradient_updated_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:29:06.939465+00:00
-- url     : https://prove2.me/theorems/08173d5d-9128-4dc2-a769-bb4d861c1204
-- title:
--   BDL26 RXXStar Transport: gradient updated x
-- statement:
--   The updated X error is the genuine nonzero local gradient; no choice of potential is identified with the witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L482-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L482-L512

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

theorem QEC.Coding.BDL26RXXStarTransport.gradient_updated_x (x : XCoord S i) (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      (updated S depth i h a (a+gradientError S depth i h x)) = boundaryGradient S depth i h x := by sorry
