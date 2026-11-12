-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_error_localized
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.error_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:42:14.493202+00:00
-- url     : https://prove2.me/theorems/513498b0-7a27-4bf3-93c0-c9fb1b6d4c0b
-- title:
--   BDL26 RXActive Error Transport: error localized
-- statement:
--   The BDL26 RXActive Error Transport construction uses the error localized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L177-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L177-L186

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.error_localized (E : Upper S depth i) :
    hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h (activeX S depth i h E) ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h (activeQ S depth i h E) := by sorry
