-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_two_run
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T15:39:29.871393+00:00
-- url     : https://prove2.me/theorems/8ac0d3c8-ad91-4fa6-9883-6ed90244ec87
-- title:
--   BDL26 RXFinite Block Transport: two run
-- statement:
--   Full finite-set transport, with the internally fixed potential and literal root word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L601-L612
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L601-L612

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_two_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.two_run (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h X0 a b) =
        updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b) ∧
      (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h X0 a b) =
        (coarseSum S depth i h a b).val ∧
      hammingSupport (Phi S depth i h X0 a b) ⊆ degreeZeroBlocks S depth i h X0 ∧
      hammingSupport (L S depth i h X0 a b) ⊆ neighbors S depth i X0 Q0 ∧
      hammingSupport (coarseSum S depth i h a b).val ⊆ neighborZ S depth i X0 Q0 := by sorry
