-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_singleton_q
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.lower_singleton_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:32:38.794631+00:00
-- url     : https://prove2.me/theorems/f213eda3-e0ab-40eb-a61b-3dcb7e9aef6b
-- title:
--   BDL26 RXFinite Block Transport: lower singleton q
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the lower singleton q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L586-L598
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L586-L598

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.lower_singleton_q (q : QCoord S i) (a b : Upper S depth i)
    (he : Localized S depth i h ∅ {q} a b) :
    L S depth i h ∅ a b=BDL26RXQBlockTransport.lowerWord S depth i h q a b := by sorry
