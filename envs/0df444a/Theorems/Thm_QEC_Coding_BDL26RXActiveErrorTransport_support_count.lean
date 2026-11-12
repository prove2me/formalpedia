-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_support_count
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.support_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:40:22.625386+00:00
-- url     : https://prove2.me/theorems/62c2c2e3-190d-49e8-9a60-c4027e6638d8
-- title:
--   BDL26 RXActive Error Transport: support count
-- statement:
--   The BDL26 RXActive Error Transport construction uses the support count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L201-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L201-L208

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.support_count (E : Upper S depth i) :
    (∑ x ∈ activeX S depth i h E, (xPiece S depth i h E x).card) +
      (∑ q ∈ activeQ S depth i h E, (qPiece S depth i h E q).card)=HammingWeight E := by sorry
