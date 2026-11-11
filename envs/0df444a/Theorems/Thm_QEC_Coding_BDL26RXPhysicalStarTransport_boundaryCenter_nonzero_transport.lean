-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_nonzero_transport
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_nonzero_transport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:13:49.081849+00:00
-- url     : https://prove2.me/theorems/c5e5dcc8-9b70-456c-b5f9-585da3922442
-- title:
--   BDL26 RXPhysical Star Transport: boundary Center nonzero transport
-- statement:
--   Nonzero original closed error and nonzero fixed potential boundary, for arbitrary backgrounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L452-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L452-L486

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_nonzero_transport (x : XCoord S i) (a : Upper S depth i) :
    let u := boundaryCenter S depth i h x
    let b := a+gradient S depth i u
    gradient S depth i u≠0 ∧ updated S depth i h a b≠0 ∧
    (run S depth i h b).correction=(run S depth i h a).correction ∧
    (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b)≠0 ∧
    (coarseSum S depth i h a b).val=0 ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=0 ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      gradient S depth i u+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) := by sorry
