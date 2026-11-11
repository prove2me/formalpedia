-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_shift_oneX
-- name    : QEC.Coding.BDL26RXXStarTransport.gradient_shift_oneX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:29:20.411859+00:00
-- url     : https://prove2.me/theorems/b9240c3e-8d19-410b-91e9-2bae142f9a67
-- title:
--   BDL26 RXXStar Transport: gradient shift one X
-- statement:
--   Strict one-X input support holds for every original background.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L442-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L442-L446

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

theorem QEC.Coding.BDL26RXXStarTransport.gradient_shift_oneX (x : XCoord S i) (a : Upper S depth i) :
    OneX S depth i h x a (a+gradientError S depth i h x) := by sorry
