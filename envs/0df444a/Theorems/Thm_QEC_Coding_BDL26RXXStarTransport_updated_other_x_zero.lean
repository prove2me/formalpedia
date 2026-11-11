-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_updated_other_x_zero
-- name    : QEC.Coding.BDL26RXXStarTransport.updated_other_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:02:20.464478+00:00
-- url     : https://prove2.me/theorems/82539fa9-7099-487e-aaf2-24a0c93bfd0d
-- title:
--   BDL26 RXXStar Transport: updated other x zero
-- statement:
--   The BDL26 RXXStar Transport construction uses the updated other x zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L213-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L213-L223

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

theorem QEC.Coding.BDL26RXXStarTransport.updated_other_x_zero (x y : XCoord S i) (hy : y≠x) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) (updated S depth i h a b)=0 := by sorry
