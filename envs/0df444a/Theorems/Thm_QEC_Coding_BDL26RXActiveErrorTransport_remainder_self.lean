-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_remainder_self
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.remainder_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:59:56.992758+00:00
-- url     : https://prove2.me/theorems/3bdbe839-14bd-41f8-b7ff-026a8b4a9053
-- title:
--   BDL26 RXActive Error Transport: remainder self
-- statement:
--   The BDL26 RXActive Error Transport construction uses the remainder self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L397-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L397-L398

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_remainder_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_remainder_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.remainder_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.remainder_self


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

theorem QEC.Coding.BDL26RXActiveErrorTransport.remainder_self (a : Upper S depth i) : R S depth i h a a=0 := by sorry
