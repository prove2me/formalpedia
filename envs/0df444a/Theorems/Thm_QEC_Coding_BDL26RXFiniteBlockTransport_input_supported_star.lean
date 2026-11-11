-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_input_supported_star
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.input_supported_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:30:03.67621+00:00
-- url     : https://prove2.me/theorems/58b611e4-1fc5-40d0-b02a-a4033acd996d
-- title:
--   BDL26 RXFinite Block Transport: input supported star
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the input supported star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L264-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L264-L272

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.input_supported_star (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (a+b) ⊆ star S depth i h X0 Q0 := by sorry
