-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_count_le_weight
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.active_count_le_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:24:16.395211+00:00
-- url     : https://prove2.me/theorems/cba39d17-8c6d-44dd-986f-91afb2beccfb
-- title:
--   BDL26 RXActive Error Transport: active count le weight
-- statement:
--   The BDL26 RXActive Error Transport construction uses the active count le weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L210-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L210-L222

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.active_count_le_weight (E : Upper S depth i) :
    (activeX S depth i h E).card+(activeQ S depth i h E).card ≤ HammingWeight E := by sorry
