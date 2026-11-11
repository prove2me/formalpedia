-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_self
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.remainder_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:43:19.422198+00:00
-- url     : https://prove2.me/theorems/48a3c8f4-08cb-46c0-878d-58964d83e53f
-- title:
--   BDL26 RXFinite Block Transport: remainder self
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the remainder self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L552-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L552-L553

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.remainder_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.remainder_self (X0 : Finset (XCoord S i)) (a : Upper S depth i) : R S depth i h X0 a a=0 := by sorry
