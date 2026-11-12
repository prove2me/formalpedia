-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_remainder_x_zero
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.remainder_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:50:31.803749+00:00
-- url     : https://prove2.me/theorems/b2a7ca9c-84b9-46d7-b6a5-7f6d91ddbfed
-- title:
--   BDL26 RXActive Error Transport: remainder x zero
-- statement:
--   The BDL26 RXActive Error Transport construction uses the remainder x zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L314-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L314-L316

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_x_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXActiveErrorTransport.remainder_x_zero (a b : Upper S depth i) (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x) (R S depth i h a b)=0 := by sorry
