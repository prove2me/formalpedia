-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_support_partition
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.support_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:15:50.020021+00:00
-- url     : https://prove2.me/theorems/ae0e6bd3-34f0-4d73-9a09-b6c53b617555
-- title:
--   BDL26 RXActive Error Transport: support partition
-- statement:
--   Exact labelled partition of full physical ERROR support, with empty pieces omitted only as inactive labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L151-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L151-L175

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.support_partition (E : Upper S depth i) :
    (activeX S depth i h E).biUnion (xPiece S depth i h E) ∪
      (activeQ S depth i h E).biUnion (qPiece S depth i h E)=hammingSupport E := by sorry
