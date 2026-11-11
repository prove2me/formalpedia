-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_flow_nonincident_q
-- name    : QEC.Coding.BDL26RXXStarTransport.x_flow_nonincident_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:43:18.927704+00:00
-- url     : https://prove2.me/theorems/2d2dd20f-0a45-444e-9c2d-326ce69e5058
-- title:
--   BDL26 RXXStar Transport: x flow nonincident q
-- statement:
--   A nonincident Q has no outgoing X-flow contribution. This uses the original
--   directed graph, and does not apply the staged Q formula to a nonzero X error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L156-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L156-L170

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

theorem QEC.Coding.BDL26RXXStarTransport.x_flow_nonincident_q (x : XCoord S i) (q : QCoord S i)
    (hxq : q ∉ incidentQ S depth i x)
    (f : Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).correctionRegion x))) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      ((rxContract S depth i h).support_decomposition.cxFlow x f)=0 := by sorry
