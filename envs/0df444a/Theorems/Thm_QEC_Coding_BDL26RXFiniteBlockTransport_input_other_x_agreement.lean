-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_input_other_x_agreement
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.input_other_x_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:21:40.527209+00:00
-- url     : https://prove2.me/theorems/bb7d0260-a816-44d7-b229-8c4a094216a5
-- title:
--   BDL26 RXFinite Block Transport: input other x agreement
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the input other x agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L116-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L116-L125

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_input_other_x_agreement

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.input_other_x_agreement (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i b).val := by sorry
