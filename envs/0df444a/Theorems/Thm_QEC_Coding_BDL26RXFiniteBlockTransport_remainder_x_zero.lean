-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_x_zero
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.remainder_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:36:44.676861+00:00
-- url     : https://prove2.me/theorems/e0ea9090-709d-47eb-8a1d-94670aea2129
-- title:
--   BDL26 RXFinite Block Transport: remainder x zero
-- statement:
--   Every actual X ERROR restriction vanishes before the Cq argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L364-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L364-L371

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_x_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.remainder_x_zero (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (R S depth i h X0 a b)=0 := by sorry
