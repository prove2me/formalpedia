-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential
-- name    : QEC.Coding.BDL26RXXStarTransport.map1_with_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:56:13.203464+00:00
-- url     : https://prove2.me/theorems/a37c2530-3657-4ba4-9fcc-c148838696bf
-- title:
--   BDL26 RXXStar Transport: map1 with potential
-- statement:
--   The BDL26 RXXStar Transport construction uses the map1 with potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L329-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L329-L333

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.map1_with_potential (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ
        (potential S depth i h x a b) := by sorry
