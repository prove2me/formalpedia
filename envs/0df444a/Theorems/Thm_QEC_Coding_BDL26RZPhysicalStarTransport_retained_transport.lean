-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_retained_transport
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.retained_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:41:54.592098+00:00
-- url     : https://prove2.me/theorems/95ccd9aa-3f89-4a83-aee6-8cf4cb2d71b6
-- title:
--   BDL26 RZPhysical Star Transport: retained transport
-- statement:
--   Every copy and subdivision coordinate gives a genuine actual nonzero example.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L482-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L482-L494

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.retained_transport (above : 3 ≤ i.val) (a : Upper S depth i) (copy : BDL26FiniteTannerSquare.Two)
    (v : QSubdivisionVertex (transposePresentation (Old S depth i)) (retainedQ S depth i) S) :
    let q := retainedQ S depth i
    let z := retainedZ S depth i
    let u := qCentre S depth i odd q z (retained_incidence S depth i) (copy,v)
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q (copy,v))
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z z) ∧
      parent S (i.val+1) (Vertex.q (physicalQ S depth i odd q (copy,v)))=some (Vertex.q q) ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 7 := by sorry
