-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_self
-- name    : QEC.Coding.BDL26RXXStarTransport.remainder_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:54:50.603108+00:00
-- url     : https://prove2.me/theorems/374bd3af-c69c-4c48-a02f-d7995eeae60a
-- title:
--   BDL26 RXXStar Transport: remainder self
-- statement:
--   The BDL26 RXXStar Transport construction uses the remainder self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L429-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L429-L431

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

theorem QEC.Coding.BDL26RXXStarTransport.remainder_self (x : XCoord S i) (a : Upper S depth i) :
    remainder S depth i h x a a=0 := by sorry
