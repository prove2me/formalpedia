-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_gradient_pair_consumer
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_consumer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:53:47.884552+00:00
-- url     : https://prove2.me/theorems/4eb0c47d-0e23-4a46-925a-11ce596ef379
-- title:
--   BDL26 RXActive Error Transport: gradient pair consumer
-- statement:
--   The BDL26 RXActive Error Transport construction uses the gradient pair consumer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L525-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L525-L538

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_consumer

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_consumer (x0 x1 : XCoord S i) (hn : x0≠x1) (a : Upper S depth i) :
    let b := a+(gradientError S depth i h x0+gradientError S depth i h x1)
    activeX S depth i h (a+b)={x0,x1} ∧ activeQ S depth i h (a+b)=∅ ∧
      Phi S depth i h a b≠0 ∧ (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b)≠0 ∧
      ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h a b) =
        updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h a b)=(coarseSum S depth i h a b).val ∧
      HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) := by sorry
