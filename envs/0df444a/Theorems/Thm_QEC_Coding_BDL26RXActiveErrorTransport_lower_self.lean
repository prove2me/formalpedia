-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_self
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.lower_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:04:05.030744+00:00
-- url     : https://prove2.me/theorems/e22b1786-0be0-455b-a147-0165cfec9212
-- title:
--   BDL26 RXActive Error Transport: lower self
-- statement:
--   The BDL26 RXActive Error Transport construction uses the lower self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L400-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L400-L401

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_self
attribute [local simp] QEC.Coding.BDL26RXFiniteBlockTransport.lower_self


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

theorem QEC.Coding.BDL26RXActiveErrorTransport.lower_self (a : Upper S depth i) : L S depth i h a a=0 := by sorry
