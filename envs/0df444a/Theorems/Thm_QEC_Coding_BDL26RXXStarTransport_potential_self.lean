-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_self
-- name    : QEC.Coding.BDL26RXXStarTransport.potential_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:54:58.533427+00:00
-- url     : https://prove2.me/theorems/216d0806-66de-4483-bab2-c4d4d146c3c8
-- title:
--   BDL26 RXXStar Transport: potential self
-- statement:
--   The BDL26 RXXStar Transport construction uses the potential self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L425-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L425-L427

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

theorem QEC.Coding.BDL26RXXStarTransport.potential_self (x : XCoord S i) (a : Upper S depth i) :
    potential S depth i h x a a=0 := by sorry
