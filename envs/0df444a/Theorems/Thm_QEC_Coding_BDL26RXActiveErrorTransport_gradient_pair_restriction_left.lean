-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_restriction_left
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_restriction_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:27:26.415944+00:00
-- url     : https://prove2.me/theorems/7f47dc23-faa2-49ea-bb19-8581cab2ab84
-- title:
--   BDL26 RXActive Error Transport: gradient pair restriction left
-- statement:
--   The BDL26 RXActive Error Transport construction uses the gradient pair restriction left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L463-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L463-L468

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_restriction_left (x0 x1 : XCoord S i) (hn : x0≠x1) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x0)
      (gradientError S depth i h x0+gradientError S depth i h x1)=boundaryGradient S depth i h x0 := by sorry
