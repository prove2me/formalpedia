-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_incidentQ
-- name    : QEC.Coding.BDL26RXXStarTransport.mem_incidentQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:17:25.856715+00:00
-- url     : https://prove2.me/theorems/0b8899cf-b478-44b6-9c46-addad20d1ce5
-- title:
--   BDL26 RXXStar Transport: mem incident Q
-- statement:
--   The BDL26 RXXStar Transport construction uses the mem incident Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L48-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L48-L50

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

theorem QEC.Coding.BDL26RXXStarTransport.mem_incidentQ (x : XCoord S i) (q : QCoord S i) :
    q ∈ incidentQ S depth i x ↔ (state S i.val).presentation.xq x q=true := by sorry
