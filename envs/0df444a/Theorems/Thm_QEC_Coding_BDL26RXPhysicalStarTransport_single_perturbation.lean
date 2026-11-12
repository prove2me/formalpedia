-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_single_perturbation
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.single_perturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:08:58.079234+00:00
-- url     : https://prove2.me/theorems/fb3ef407-a603-448d-804f-9c04d6f85e0a
-- title:
--   BDL26 RXPhysical Star Transport: single perturbation
-- statement:
--   The complete single-physical-perturbation relation includes its actual computed parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L372-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L372-L387

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.single_perturbation (p : FamilyQ S depth i.succ) (a : Upper S depth i) :
    let u := perturbationCenter S depth i p
    let b := a+canonicalBasisWord p
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport (L S depth i h u a b) ⊆
      physicalXStar (state S i.val).presentation (parentX S depth i h u) ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by sorry
