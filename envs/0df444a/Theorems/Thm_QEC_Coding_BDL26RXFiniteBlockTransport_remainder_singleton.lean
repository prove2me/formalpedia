-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_singleton
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.remainder_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:58:35.821143+00:00
-- url     : https://prove2.me/theorems/71c8f08c-ee5d-441b-a393-e14d1446e96b
-- title:
--   BDL26 RXFinite Block Transport: remainder singleton
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the remainder singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L576-L579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L576-L579

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.remainder_singleton (x : XCoord S i) (a b : Upper S depth i) :
    R S depth i h {x} a b=BDL26RXXStarTransport.remainder S depth i h x a b := by sorry
