-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_localized
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:18:18.056948+00:00
-- url     : https://prove2.me/theorems/6dba4366-84a2-4ff0-8c81-e8e032677062
-- title:
--   BDL26 RXFinite Block Transport: gradient pair localized
-- statement:
--   Two distinct owners are kept as two original labels, even at a shared Q block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L637-L647
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L637-L647

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_localized (x0 x1 : XCoord S i) (a : Upper S depth i) :
    Localized S depth i h {x0,x1} ∅ a
      (a+(gradientError S depth i h x0+gradientError S depth i h x1)) := by sorry
