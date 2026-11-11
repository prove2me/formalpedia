-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_gradient_pair_consumer
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_consumer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:32:55.613709+00:00
-- url     : https://prove2.me/theorems/6a4873e8-1c64-4c05-bd41-c1e99df50915
-- title:
--   BDL26 RXFinite Block Transport: gradient pair consumer
-- statement:
--   Overlap consumer with arbitrary original background and complete original runs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L701-L718
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L701-L718

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.gradient_pair_consumer (x0 x1 : XCoord S i) (hne : x0≠x1) (a : Upper S depth i) :
    let b := a+(gradientError S depth i h x0+gradientError S depth i h x1)
    Localized S depth i h {x0,x1} ∅ a b ∧
      restrictWordLinear ((rxLx S depth i h).correctionRegion x0) (updated S depth i h a b) =
        boundaryGradient S depth i h x0 ∧
      restrictWordLinear ((rxLx S depth i h).correctionRegion x1) (updated S depth i h a b) =
        boundaryGradient S depth i h x1 ∧
      Phi S depth i h {x0,x1} a b≠0 ∧
      (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h {x0,x1} a b)≠0 ∧
      ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h {x0,x1} a b) =
        updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h {x0,x1} a b) := by sorry
