-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_both_empty_error_zero
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.both_empty_error_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:01:50.659283+00:00
-- url     : https://prove2.me/theorems/5573b85f-5c41-4b98-b259-7169b9a58a16
-- title:
--   BDL26 RXFinite Block Transport: both empty error zero
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the both empty error zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L568-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L568-L571

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.both_empty_error_zero (a b : Upper S depth i) (he : Localized S depth i h ∅ ∅ a b) : a+b=0 := by sorry
