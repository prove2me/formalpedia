-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradient_potential_nonzero
-- name    : QEC.Coding.BDL26RXXStarTransport.gradient_potential_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:30:00.562812+00:00
-- url     : https://prove2.me/theorems/0c20d102-dbd5-4371-9deb-a8dd081a2dbe
-- title:
--   BDL26 RXXStar Transport: gradient potential nonzero
-- statement:
--   The BDL26 RXXStar Transport construction uses the gradient potential nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L522-L526
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L522-L526

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

theorem QEC.Coding.BDL26RXXStarTransport.gradient_potential_nonzero (x : XCoord S i) (a : Upper S depth i) :
    potential S depth i h x a (a+gradientError S depth i h x) ≠ 0 := by sorry
