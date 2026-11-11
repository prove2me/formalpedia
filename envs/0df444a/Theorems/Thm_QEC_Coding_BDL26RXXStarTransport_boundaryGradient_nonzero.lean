-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundaryGradient_nonzero
-- name    : QEC.Coding.BDL26RXXStarTransport.boundaryGradient_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:31:48.166932+00:00
-- url     : https://prove2.me/theorems/75b9443f-6ecc-40dd-9f2f-07dc9d8e494c
-- title:
--   BDL26 RXXStar Transport: boundary Gradient nonzero
-- statement:
--   The BDL26 RXXStar Transport construction uses the boundary Gradient nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L252-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L252-L257

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

theorem QEC.Coding.BDL26RXXStarTransport.boundaryGradient_nonzero (x : XCoord S i) : boundaryGradient S depth i h x ≠ 0 := by sorry
