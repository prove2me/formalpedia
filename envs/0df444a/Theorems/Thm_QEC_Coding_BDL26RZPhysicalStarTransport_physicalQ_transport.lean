-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_physicalQ_transport
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:39:55.553205+00:00
-- url     : https://prove2.me/theorems/801cac37-0cbd-4eb0-bd2f-a4a90ce229a1
-- title:
--   BDL26 RZPhysical Star Transport: physical Q transport
-- statement:
--   Both raw parents and the nonzero lower word accompany the complete pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L382-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L382-L401

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_transport (above : 3 ≤ i.val) (a : Upper S depth i)
    (q : (Old S depth i).Q) (z : (Old S depth i).Z) (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    let u := qCentre S depth i odd q z hqz v
    let r := physicalQ S depth i odd q v
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z z) ∧
      parent S (i.val+1) (Vertex.q r)=some (Vertex.q q) ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 7 := by sorry
