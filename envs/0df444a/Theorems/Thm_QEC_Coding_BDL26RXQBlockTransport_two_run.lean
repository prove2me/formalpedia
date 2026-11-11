-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run
-- name    : QEC.Coding.BDL26RXQBlockTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:29:28.001142+00:00
-- url     : https://prove2.me/theorems/8ae2bc55-d69c-419d-a08c-84817e704e27
-- title:
--   BDL26 RXQBlock Transport: two run
-- statement:
--   A named complete construction, retaining its full zero potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L486-L497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L486-L497

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.two_run (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h q a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (potential S depth i h) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerWord S depth i h q a b) =
        (coarseSum S depth i h a b).val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val =
        (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h))=0 := by sorry
