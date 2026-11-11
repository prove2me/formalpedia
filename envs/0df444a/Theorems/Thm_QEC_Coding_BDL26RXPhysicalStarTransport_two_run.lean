-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_two_run
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:14:21.158475+00:00
-- url     : https://prove2.me/theorems/22201103-9c72-4f83-b792-faccfcb27816
-- title:
--   BDL26 RXPhysical Star Transport: two run
-- statement:
--   One complete same-run error/correction/stabilizer theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L280-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L280-L296

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_two_run
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_two_run

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.two_run (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    parent S (i.val+1) (Vertex.x u)=some (Vertex.x (parentX S depth i h u)) ∧
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b+(indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) ∧
    (indexedFamily S depth).coboundary1 i.castSucc (L S depth i h u a b)=
      (coarseSum S depth i h a b).val ∧
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h (parentX S depth i h u) ∧
    hammingSupport (Phi S depth i h u a b) ⊆ degreeZeroBlock S depth i h (parentX S depth i h u) ∧
    hammingSupport (L S depth i h u a b) ⊆
      physicalXStar (state S i.val).presentation (parentX S depth i h u) ∧
    HammingWeight (L S depth i h u a b) ≤ 7 := by sorry
