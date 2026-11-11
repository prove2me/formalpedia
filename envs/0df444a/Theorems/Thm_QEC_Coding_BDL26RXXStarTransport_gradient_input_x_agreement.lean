-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_input_x_agreement
-- name    : QEC.Coding.BDL26RXXStarTransport.gradient_input_x_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:30:53.747207+00:00
-- url     : https://prove2.me/theorems/09ead50d-3ac2-40c0-9c53-234f2598033a
-- title:
--   BDL26 RXXStar Transport: gradient input x agreement
-- statement:
--   The BDL26 RXXStar Transport construction uses the gradient input x agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L448-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L448-L465

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

theorem QEC.Coding.BDL26RXXStarTransport.gradient_input_x_agreement (x y : XCoord S i) (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y)
        (errorSyndrome S depth i (a+gradientError S depth i h x)).val := by sorry
