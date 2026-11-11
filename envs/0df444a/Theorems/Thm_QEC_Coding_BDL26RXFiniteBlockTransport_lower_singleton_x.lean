-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_singleton_x
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.lower_singleton_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:58:55.121043+00:00
-- url     : https://prove2.me/theorems/1c009a2a-6981-44d3-8fc6-1cba09eaaa29
-- title:
--   BDL26 RXFinite Block Transport: lower singleton x
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the lower singleton x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L581-L584
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L581-L584

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.lower_singleton_x (x : XCoord S i) (a b : Upper S depth i) :
    L S depth i h {x} a b=BDL26RXXStarTransport.lowerWord S depth i h x a b := by sorry
