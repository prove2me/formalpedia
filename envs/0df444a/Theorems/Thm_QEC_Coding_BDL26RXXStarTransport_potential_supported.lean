-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_supported
-- name    : QEC.Coding.BDL26RXXStarTransport.potential_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:07:46.50643+00:00
-- url     : https://prove2.me/theorems/212aa7d1-d434-48a6-b53d-179a74e25380
-- title:
--   BDL26 RXXStar Transport: potential supported
-- statement:
--   The BDL26 RXXStar Transport construction uses the potential supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L188-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L188-L190

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

theorem QEC.Coding.BDL26RXXStarTransport.potential_supported (x : XCoord S i) (a b : Upper S depth i) :
    hammingSupport (potential S depth i h x a b) ⊆ degreeZeroBlock S depth i h x := by sorry
