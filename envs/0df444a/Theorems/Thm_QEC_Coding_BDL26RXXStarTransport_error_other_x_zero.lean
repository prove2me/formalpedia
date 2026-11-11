-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_error_other_x_zero
-- name    : QEC.Coding.BDL26RXXStarTransport.error_other_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:31:23.333595+00:00
-- url     : https://prove2.me/theorems/dad2762e-dbf5-47fa-a492-f56220612bf1
-- title:
--   BDL26 RXXStar Transport: error other x zero
-- statement:
--   The BDL26 RXXStar Transport construction uses the error other x zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L112-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L112-L120

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

theorem QEC.Coding.BDL26RXXStarTransport.error_other_x_zero (x y : XCoord S i) (hy : y≠x)
    (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) e=0 := by sorry
