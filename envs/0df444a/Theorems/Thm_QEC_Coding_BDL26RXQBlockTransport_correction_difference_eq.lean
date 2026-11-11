-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_eq
-- name    : QEC.Coding.BDL26RXQBlockTransport.correction_difference_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:55:45.83171+00:00
-- url     : https://prove2.me/theorems/9734719a-b893-4af8-a22c-5628b63a3539
-- title:
--   BDL26 RXQBlock Transport: correction difference eq
-- statement:
--   Every original X component and every other original Q component cancels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L228-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L228-L251

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

theorem QEC.Coding.BDL26RXQBlockTransport.correction_difference_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    (run S depth i h a).correction + (run S depth i h b).correction =
      cqComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val q +
        cqComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val q := by sorry
