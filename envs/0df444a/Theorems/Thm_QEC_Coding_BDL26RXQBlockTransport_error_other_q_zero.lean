-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_error_other_q_zero
-- name    : QEC.Coding.BDL26RXQBlockTransport.error_other_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:05:41.178795+00:00
-- url     : https://prove2.me/theorems/489b31c4-2dea-4d55-9238-78ab79ac3c13
-- title:
--   BDL26 RXQBlock Transport: error other q zero
-- statement:
--   The BDL26 RXQBlock Transport construction uses the error other q zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L180-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L180-L185

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

theorem QEC.Coding.BDL26RXQBlockTransport.error_other_q_zero (q : QCoord S i) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLq S depth i h).correctionRegion q)
    (r : QCoord S i) (hr : r≠q) :
    restrictWordLinear ((rxLq S depth i h).correctionRegion r) e=0 := by sorry
