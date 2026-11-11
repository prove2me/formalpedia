-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_error_x_zero
-- name    : QEC.Coding.BDL26RXQBlockTransport.error_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:32:18.516196+00:00
-- url     : https://prove2.me/theorems/e097d49b-3d9a-45b6-a243-3067e1969231
-- title:
--   BDL26 RXQBlock Transport: error x zero
-- statement:
--   Original Q-supported errors have zero actual X restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L169-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L169-L178

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

theorem QEC.Coding.BDL26RXQBlockTransport.error_x_zero (q : QCoord S i) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLq S depth i h).correctionRegion q)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).correctionRegion x) e=0 := by sorry
