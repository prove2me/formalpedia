-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundarySingleton_vertical
-- name    : QEC.Coding.BDL26RXXStarTransport.boundarySingleton_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:47:31.759781+00:00
-- url     : https://prove2.me/theorems/a1ae3685-0cff-45dd-830c-8fe28c8250c1
-- title:
--   BDL26 RXXStar Transport: boundary Singleton vertical
-- statement:
--   The BDL26 RXXStar Transport construction uses the boundary Singleton vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L237-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L237-L246

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.boundarySingleton_vertical (x : XCoord S i) :
    wordLinearMapTranspose (doubleCylinderBoundary1 (state S i.val).presentation x S)
      (boundarySingleton S depth i x) (Sum.inr (boundaryVertex S depth i x)) = 1 := by sorry
