-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_potential_self
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.potential_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:36:05.058535+00:00
-- url     : https://prove2.me/theorems/8bdaec16-7a7b-498d-a93f-bc080a96c830
-- title:
--   BDL26 RXActive Error Transport: potential self
-- statement:
--   The BDL26 RXActive Error Transport construction uses the potential self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L394-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L394-L395

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_self
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.potential_self


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

theorem QEC.Coding.BDL26RXActiveErrorTransport.potential_self (a : Upper S depth i) : Phi S depth i h a a=0 := by sorry
