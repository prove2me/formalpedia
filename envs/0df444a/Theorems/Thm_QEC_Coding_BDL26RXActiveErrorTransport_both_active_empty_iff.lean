-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_both_active_empty_iff
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.both_active_empty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:45:36.328557+00:00
-- url     : https://prove2.me/theorems/e9837bf8-9d8f-48f0-907f-6322f8edbd7a
-- title:
--   BDL26 RXActive Error Transport: both active empty iff
-- statement:
--   The BDL26 RXActive Error Transport construction uses the both active empty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L230-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L230-L242

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.both_active_empty_iff (E : Upper S depth i) :
    activeX S depth i h E=∅ ∧ activeQ S depth i h E=∅ ↔ E=0 := by sorry
