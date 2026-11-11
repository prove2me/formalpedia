-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_localPotential_boundary
-- name    : QEC.Coding.BDL26RXXStarTransport.localPotential_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:27:23.799196+00:00
-- url     : https://prove2.me/theorems/0c4a7494-81f6-482e-a4a4-2f53e03b04b0
-- title:
--   BDL26 RXXStar Transport: local Potential boundary
-- statement:
--   The BDL26 RXXStar Transport construction uses the local Potential boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L173-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L173-L179

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

theorem QEC.Coding.BDL26RXXStarTransport.localPotential_boundary (x : XCoord S i) (a b : Upper S depth i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta0 x (localPotential S depth i h x a b) =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) := by sorry
