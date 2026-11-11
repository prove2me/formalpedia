-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_phi_nonzero
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_phi_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:21:31.06532+00:00
-- url     : https://prove2.me/theorems/d13cb21d-20e3-4344-8519-0cdf429f4d4d
-- title:
--   BDL26 RXFinite Block Transport: gradient pair phi nonzero
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the gradient pair phi nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L692-L698
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L692-L698

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_phi_nonzero (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    Phi S depth i h {x0,x1} a
      (a+(gradientError S depth i h x0+gradientError S depth i h x1)) ≠ 0 := by sorry
