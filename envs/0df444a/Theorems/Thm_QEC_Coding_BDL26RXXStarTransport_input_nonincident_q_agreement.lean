-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_input_nonincident_q_agreement
-- name    : QEC.Coding.BDL26RXXStarTransport.input_nonincident_q_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:27:13.161396+00:00
-- url     : https://prove2.me/theorems/f06f75b7-7c58-4575-a7ca-b265f00de894
-- title:
--   BDL26 RXXStar Transport: input nonincident q agreement
-- statement:
--   The BDL26 RXXStar Transport construction uses the input nonincident q agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L37-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L37-L44

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

theorem QEC.Coding.BDL26RXXStarTransport.input_nonincident_q_agreement (x : XCoord S i) (q : QCoord S i)
    (hq : q ∉ incidentQ S depth i x) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q) (errorSyndrome S depth i b).val := by sorry
