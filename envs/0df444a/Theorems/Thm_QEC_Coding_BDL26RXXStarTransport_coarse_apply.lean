-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply
-- name    : QEC.Coding.BDL26RXXStarTransport.coarse_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:00:38.110596+00:00
-- url     : https://prove2.me/theorems/01366842-4fea-4d56-9df4-122f5ebeb543
-- title:
--   BDL26 RXXStar Transport: coarse apply
-- statement:
--   The original labelled F₂ sum retains all incident labels and cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L358-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L358-L369

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

theorem QEC.Coding.BDL26RXXStarTransport.coarse_apply (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ incidentQ S depth i x, lowerWord S depth i h x a b q *
        (if (state S i.val).presentation.qz q z=true then 1 else 0) := by sorry
