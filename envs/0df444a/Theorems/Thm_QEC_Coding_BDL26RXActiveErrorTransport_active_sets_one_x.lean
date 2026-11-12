-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_sets_one_x
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.active_sets_one_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:53:24.131201+00:00
-- url     : https://prove2.me/theorems/e3acef66-aabc-4b9f-bb40-53a6438c0b8c
-- title:
--   BDL26 RXActive Error Transport: active sets one x
-- statement:
--   The BDL26 RXActive Error Transport construction uses the active sets one x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L439-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L439-L449

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXActiveErrorTransport.active_sets_one_x (x : XCoord S i) (E : Upper S depth i)
    (he : hammingSupport E ⊆ (rxLx S depth i h).correctionRegion x)
    (hn : restrictWordLinear ((rxLx S depth i h).correctionRegion x) E≠0) :
    activeX S depth i h E={x} ∧ activeQ S depth i h E=∅ := by sorry
