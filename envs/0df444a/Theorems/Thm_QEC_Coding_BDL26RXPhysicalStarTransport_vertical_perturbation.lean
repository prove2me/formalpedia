-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_vertical_perturbation
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.vertical_perturbation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:13:47.907486+00:00
-- url     : https://prove2.me/theorems/2317dafc-a17b-41ba-a6fd-092e2dda106d
-- title:
--   BDL26 RXPhysical Star Transport: vertical perturbation
-- statement:
--   One nonzero actual connector perturbation, with all transport outputs retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L531-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L531-L566

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.vertical_perturbation (x : XCoord S i) (a : Upper S depth i) :
    let u := boundaryCenter S depth i h x
    let p := verticalPhysical S depth i h x
    let b := a+canonicalBasisWord p
    (canonicalBasisWord p : Upper S depth i)≠0 ∧
    parent S (i.val+1) (Vertex.q p)=none ∧
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x x) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport (L S depth i h u a b) ⊆ physicalXStar (state S i.val).presentation x ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by sorry
