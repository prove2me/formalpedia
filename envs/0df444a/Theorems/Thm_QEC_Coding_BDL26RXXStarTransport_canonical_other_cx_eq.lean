-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_canonical_other_cx_eq
-- name    : QEC.Coding.BDL26RXXStarTransport.canonical_other_cx_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:07:39.311893+00:00
-- url     : https://prove2.me/theorems/38bdced3-cdda-4cfe-80bc-91f144a0eadb
-- title:
--   BDL26 RXXStar Transport: canonical other cx eq
-- statement:
--   The BDL26 RXXStar Transport construction uses the canonical other cx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L68-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L68-L72

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

theorem QEC.Coding.BDL26RXXStarTransport.canonical_other_cx_eq (x y : XCoord S i) (hy : y≠x)
    (a b : Upper S depth i) (he : OneX S depth i h x a b) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y := by sorry
