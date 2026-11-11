-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_two_run
-- name    : QEC.Coding.BDL26RXXStarTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:56:57.743207+00:00
-- url     : https://prove2.me/theorems/6411b091-db50-46a2-9343-3b92374e3717
-- title:
--   BDL26 RXXStar Transport: two run
-- statement:
--   Complete construction, retaining both actual runs and the original coarse syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L549-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L549-L559

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.two_run (x : XCoord S i) (a b : Upper S depth i) (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h x a b) =
        (coarseSum S depth i h a b).val ∧
      hammingSupport (potential S depth i h x a b) ⊆ degreeZeroBlock S depth i h x ∧
      hammingSupport (lowerWord S depth i h x a b) ⊆ incidentQ S depth i x ∧
      hammingSupport (coarseSum S depth i h a b).val ⊆ incidentZ S depth i x := by sorry
