-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_activeX_subset_of_support
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.activeX_subset_of_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:08:49.429932+00:00
-- url     : https://prove2.me/theorems/3f176253-f780-4bb8-bbf9-ec598e25fed8
-- title:
--   BDL26 RXActive Error Transport: active X subset of support
-- statement:
--   The BDL26 RXActive Error Transport construction uses the active X subset of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L411-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L411-L423

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.activeX_subset_of_support (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (E : Upper S depth i)
    (he : hammingSupport E ⊆ BDL26RXFiniteBlockTransport.xBlocks S depth i h X0 ∪
      BDL26RXFiniteBlockTransport.qBlocks S depth i h Q0) : activeX S depth i h E ⊆ X0 := by sorry
