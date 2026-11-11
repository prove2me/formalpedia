-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_starQ
-- name    : QEC.Coding.BDL26RXXStarTransport.mem_starQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:18:37.363567+00:00
-- url     : https://prove2.me/theorems/f0348a63-04a2-49a7-89f5-9c51215632d5
-- title:
--   BDL26 RXXStar Transport: mem star Q
-- statement:
--   The BDL26 RXXStar Transport construction uses the mem star Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L52-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L52-L55

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

theorem QEC.Coding.BDL26RXXStarTransport.mem_starQ (x : XCoord S i) (p : FamilyQ S depth i.succ) :
    p ∈ starQ S depth i h x ↔ ∃ q ∈ incidentQ S depth i x,
      p ∈ (rxLq S depth i h).correctionRegion q := by sorry
