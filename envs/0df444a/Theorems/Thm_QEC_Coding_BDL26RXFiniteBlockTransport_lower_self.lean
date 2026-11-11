-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_self
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.lower_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:57:15.560791+00:00
-- url     : https://prove2.me/theorems/f4e08493-08a2-45df-a84d-2ac058379f0b
-- title:
--   BDL26 RXFinite Block Transport: lower self
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the lower self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L555-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L555-L558

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.lower_self (X0 : Finset (XCoord S i)) (a : Upper S depth i) : L S depth i h X0 a a=0 := by sorry
