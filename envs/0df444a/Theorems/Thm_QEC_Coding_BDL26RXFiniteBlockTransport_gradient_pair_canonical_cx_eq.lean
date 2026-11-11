-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_canonical_cx_eq
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_canonical_cx_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:32:17.713997+00:00
-- url     : https://prove2.me/theorems/2330dd1a-b5b9-433a-9d1c-6a38e143be8f
-- title:
--   BDL26 RXFinite Block Transport: gradient pair canonical cx eq
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the gradient pair canonical cx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L649-L655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L649-L655

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_canonical_cx_eq (x0 x1 y : XCoord S i) (a : Upper S depth i) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h)
        (errorSyndrome S depth i (a+(gradientError S depth i h x0+gradientError S depth i h x1))).val y := by sorry
