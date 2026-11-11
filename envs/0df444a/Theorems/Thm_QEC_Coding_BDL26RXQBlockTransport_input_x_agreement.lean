-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_input_x_agreement
-- name    : QEC.Coding.BDL26RXQBlockTransport.input_x_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:05:37.814333+00:00
-- url     : https://prove2.me/theorems/104f4ea1-6df3-4754-84d7-3897ca1a5f1d
-- title:
--   BDL26 RXQBlock Transport: input x agreement
-- statement:
--   X syndrome read equality is derived from the original error difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L188-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L188-L197

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.input_x_agreement (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion x) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) (errorSyndrome S depth i b).val := by sorry
