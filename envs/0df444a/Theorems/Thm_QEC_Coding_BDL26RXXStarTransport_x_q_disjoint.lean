-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_q_disjoint
-- name    : QEC.Coding.BDL26RXXStarTransport.x_q_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:26:59.326884+00:00
-- url     : https://prove2.me/theorems/5baf69f0-9fba-42d4-8132-e04dcd39169f
-- title:
--   BDL26 RXXStar Transport: x q disjoint
-- statement:
--   An X block cannot meet any actual Q error block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L102-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L102-L110

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

theorem QEC.Coding.BDL26RXXStarTransport.x_q_disjoint (x : XCoord S i) (q : QCoord S i) :
    Disjoint ((rxLx S depth i h).correctionRegion x)
      ((rxLq S depth i h).correctionRegion q) := by sorry
