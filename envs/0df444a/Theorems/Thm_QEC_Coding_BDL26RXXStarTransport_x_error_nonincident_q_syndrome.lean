-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_x_error_nonincident_q_syndrome
-- name    : QEC.Coding.BDL26RXXStarTransport.x_error_nonincident_q_syndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:21:45.9673+00:00
-- url     : https://prove2.me/theorems/9c740579-1b06-4132-9742-9785f3498f66
-- title:
--   BDL26 RXXStar Transport: x error nonincident q syndrome
-- statement:
--   The BDL26 RXXStar Transport construction uses the x error nonincident q syndrome property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L172-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L172-L188

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

theorem QEC.Coding.BDL26RXXStarTransport.x_error_nonincident_q_syndrome (x : XCoord S i) (q : QCoord S i)
    (hq : q ∉ incidentQ S depth i x) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      ((indexedFamily S depth).coboundary1 i.succ e)=0 := by sorry
