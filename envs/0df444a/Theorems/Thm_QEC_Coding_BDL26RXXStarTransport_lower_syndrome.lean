-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_syndrome
-- name    : QEC.Coding.BDL26RXXStarTransport.lower_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:56:56.153136+00:00
-- url     : https://prove2.me/theorems/bfad76a7-23e5-481e-ae6c-fda847834c1c
-- title:
--   BDL26 RXXStar Transport: lower syndrome
-- statement:
--   The BDL26 RXXStar Transport construction uses the lower syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L343-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L343-L355

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_syndrome

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.lower_syndrome (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b) =
      (coarseSum S depth i h a b).val := by sorry
