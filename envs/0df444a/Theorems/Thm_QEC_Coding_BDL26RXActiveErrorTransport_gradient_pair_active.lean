-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_active
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_active
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:49:56.449521+00:00
-- url     : https://prove2.me/theorems/eedfdc02-7788-4492-8085-2b21eaac9542
-- title:
--   BDL26 RXActive Error Transport: gradient pair active
-- statement:
--   The active labels of the genuine closed local gradients come from ERROR restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L477-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L477-L500

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
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

theorem QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_active (x0 x1 : XCoord S i) (hn : x0≠x1) :
    activeX S depth i h (gradientError S depth i h x0+gradientError S depth i h x1)={x0,x1} ∧
      activeQ S depth i h (gradientError S depth i h x0+gradientError S depth i h x1)=∅ := by sorry
