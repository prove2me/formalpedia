-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_shift_active
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_shift_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:15:31.765691+00:00
-- url     : https://prove2.me/theorems/b23f36f7-4244-419b-8f6b-7c0a2605ca3a
-- title:
--   BDL26 RXActive Error Transport: gradient pair shift active
-- statement:
--   The BDL26 RXActive Error Transport construction uses the gradient pair shift active property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L505-L510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L505-L510

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_shift_active (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    let b := a+(gradientError S depth i h x0+gradientError S depth i h x1)
    activeX S depth i h (a+b)={x0,x1} ∧ activeQ S depth i h (a+b)=∅ := by sorry
