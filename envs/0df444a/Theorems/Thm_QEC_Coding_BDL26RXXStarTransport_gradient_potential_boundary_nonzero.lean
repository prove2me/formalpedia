-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_potential_boundary_nonzero
-- name    : QEC.Coding.BDL26RXXStarTransport.gradient_potential_boundary_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:29:07.528929+00:00
-- url     : https://prove2.me/theorems/eede7c19-e883-4e76-aba9-ee1060c7ab46
-- title:
--   BDL26 RXXStar Transport: gradient potential boundary nonzero
-- statement:
--   The BDL26 RXXStar Transport construction uses the gradient potential boundary nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L514-L520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L514-L520

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

theorem QEC.Coding.BDL26RXXStarTransport.gradient_potential_boundary_nonzero (x : XCoord S i) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (potential S depth i h x a (a+gradientError S depth i h x)) ≠ 0 := by sorry
