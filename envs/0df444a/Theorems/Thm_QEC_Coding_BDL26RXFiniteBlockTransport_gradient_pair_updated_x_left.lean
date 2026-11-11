-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_updated_x_left
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_updated_x_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:11:36.404214+00:00
-- url     : https://prove2.me/theorems/86c989e2-af09-460e-9dba-d0ed647cf164
-- title:
--   BDL26 RXFinite Block Transport: gradient pair updated x left
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the gradient pair updated x left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L657-L671
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L657-L671

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_updated_x_left (x0 x1 : XCoord S i) (hne : x0≠x1)
    (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x0)
      (updated S depth i h a (a+(gradientError S depth i h x0+gradientError S depth i h x1))) =
      boundaryGradient S depth i h x0 := by sorry
