-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_supported
-- name    : QEC.Coding.BDL26RXXStarTransport.coarse_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:57:47.430944+00:00
-- url     : https://prove2.me/theorems/050d66d9-88a3-4905-adbb-2c3c4c95d86c
-- title:
--   BDL26 RXXStar Transport: coarse supported
-- statement:
--   The BDL26 RXXStar Transport construction uses the coarse supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L371-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L371-L382

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

theorem QEC.Coding.BDL26RXXStarTransport.coarse_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport (coarseSum S depth i h a b).val ⊆ incidentZ S depth i x := by sorry
