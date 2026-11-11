-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_canonical_other_cq_eq
-- name    : QEC.Coding.BDL26RXQBlockTransport.canonical_other_cq_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:47:21.564528+00:00
-- url     : https://prove2.me/theorems/665054f9-45a0-4e97-8d58-072fc033f3cb
-- title:
--   BDL26 RXQBlock Transport: canonical other cq eq
-- statement:
--   The BDL26 RXQBlock Transport construction uses the canonical other cq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L219-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L219-L225

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

theorem QEC.Coding.BDL26RXQBlockTransport.canonical_other_cq_eq (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q)
    (r : QCoord S i) (hr : r≠q) :
    cqComponentTotal (Data S depth i h) (errorSyndrome S depth i a).val r =
      cqComponentTotal (Data S depth i h) (errorSyndrome S depth i b).val r := by sorry
