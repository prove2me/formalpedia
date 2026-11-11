-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_boundary_nonzero
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_boundary_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T16:12:25.724142+00:00
-- url     : https://prove2.me/theorems/0f1138ff-a604-4411-a454-91cc350e1d3c
-- title:
--   BDL26 RXActive Error Transport: gradient pair boundary nonzero
-- statement:
--   The BDL26 RXActive Error Transport construction uses the gradient pair boundary nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L518-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L518-L523

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_boundary_nonzero

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_boundary_nonzero (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary0 i.succ
      (Phi S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1)))≠0 := by sorry
