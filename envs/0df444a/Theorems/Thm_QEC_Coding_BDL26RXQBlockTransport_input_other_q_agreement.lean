-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_input_other_q_agreement
-- name    : QEC.Coding.BDL26RXQBlockTransport.input_other_q_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:45:55.500635+00:00
-- url     : https://prove2.me/theorems/144e4d85-4d5f-40f7-a1db-71f225024c87
-- title:
--   BDL26 RXQBlock Transport: input other q agreement
-- statement:
--   Q read equality uses the derived zero-X-error staged restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L200-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L200-L210

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

theorem QEC.Coding.BDL26RXQBlockTransport.input_other_q_agreement (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (r : QCoord S i) (hr : r≠q) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion r) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion r) (errorSyndrome S depth i b).val := by sorry
