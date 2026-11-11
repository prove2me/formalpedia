-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_supported
-- name    : QEC.Coding.BDL26RXXStarTransport.updated_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:01:52.334206+00:00
-- url     : https://prove2.me/theorems/fe8d28aa-3f0f-4284-8f52-0a6e442ea02a
-- title:
--   BDL26 RXXStar Transport: updated supported
-- statement:
--   The BDL26 RXXStar Transport construction uses the updated supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L138-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L138-L149

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_updated_supported

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.updated_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (updated S depth i h a b) ⊆ star1 S depth i h x := by sorry
