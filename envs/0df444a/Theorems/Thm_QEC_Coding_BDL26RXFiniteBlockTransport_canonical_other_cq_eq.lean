-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_canonical_other_cq_eq
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.canonical_other_cq_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:30:38.107211+00:00
-- url     : https://prove2.me/theorems/048bb47b-5cc0-40d8-9545-e586fdd88d6b
-- title:
--   BDL26 RXFinite Block Transport: canonical other cq eq
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the canonical other cq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L201-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L201-L230

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_canonical_other_cq_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.canonical_other_cq_eq (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (q : QCoord S i) (hq : q ∉ neighbors S depth i X0 Q0) (a b : Upper S depth i)
    (he : Localized S depth i h X0 Q0 a b) :
    cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i a).val q =
      cqComponentTotal (rxData S depth i h) (errorSyndrome S depth i b).val q := by sorry
