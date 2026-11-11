-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_empty
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.remainder_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:58:11.760425+00:00
-- url     : https://prove2.me/theorems/d5677d61-9a26-4f08-84a3-79a63f6ed9ed
-- title:
--   BDL26 RXFinite Block Transport: remainder empty
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the remainder empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L565-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L565-L566

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.remainder_empty (a b : Upper S depth i) : R S depth i h ∅ a b=updated S depth i h a b := by sorry
