-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_sets_one_q
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.active_sets_one_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:54:40.227195+00:00
-- url     : https://prove2.me/theorems/5485db97-7e28-4a1c-962c-a8fd3931b12b
-- title:
--   BDL26 RXActive Error Transport: active sets one q
-- statement:
--   The BDL26 RXActive Error Transport construction uses the active sets one q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L451-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L451-L461

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.active_sets_one_q (q : QCoord S i) (E : Upper S depth i)
    (he : hammingSupport E ⊆ (rxLq S depth i h).correctionRegion q)
    (hn : restrictWordLinear ((rxLq S depth i h).correctionRegion q) E≠0) :
    activeX S depth i h E=∅ ∧ activeQ S depth i h E={q} := by sorry
