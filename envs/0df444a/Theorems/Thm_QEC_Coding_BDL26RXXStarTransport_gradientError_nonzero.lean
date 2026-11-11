-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_nonzero
-- name    : QEC.Coding.BDL26RXXStarTransport.gradientError_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:44:50.98081+00:00
-- url     : https://prove2.me/theorems/160ff9f6-a0ce-4183-b7f4-448e5e695853
-- title:
--   BDL26 RXXStar Transport: gradient Error nonzero
-- statement:
--   The BDL26 RXXStar Transport construction uses the gradient Error nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L282-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L282-L286

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

theorem QEC.Coding.BDL26RXXStarTransport.gradientError_nonzero (x : XCoord S i) : gradientError S depth i h x ≠ 0 := by sorry
