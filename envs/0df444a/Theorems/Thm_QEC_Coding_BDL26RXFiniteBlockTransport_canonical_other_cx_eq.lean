-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_canonical_other_cx_eq
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.canonical_other_cx_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:29:51.558219+00:00
-- url     : https://prove2.me/theorems/604be962-060d-4536-9fa2-cc95e2c45ce3
-- title:
--   BDL26 RXFinite Block Transport: canonical other cx eq
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the canonical other cx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L194-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L194-L199

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_canonical_other_cx_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.canonical_other_cx_eq (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (y : XCoord S i) (hy : y ∉ X0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val y =
      cxComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val y := by sorry
