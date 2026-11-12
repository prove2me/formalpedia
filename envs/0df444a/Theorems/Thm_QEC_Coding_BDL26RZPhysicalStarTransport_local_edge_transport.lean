-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_local_edge_transport
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.local_edge_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:29:43.745434+00:00
-- url     : https://prove2.me/theorems/cbb41320-5c86-42d0-9eb0-08b9720d4a01
-- title:
--   BDL26 RZPhysical Star Transport: local edge transport
-- statement:
--   A local Z-edge perturbation has zero lower error but retains full E as a boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L424-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L424-L439

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.local_edge_transport (above : 3 ≤ i.val) (a : Upper S depth i)
    (z : (Old S depth i).Z) (e : ZDoubleCylinderEdge (Old S depth i) z S) :
    let r := upperQChart S depth i odd (.inl ⟨z,e⟩)
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r
    ∃ p : Potential S depth i, Pullback S depth i odd ∅ {z} a b p ∧
      lowerError S depth i odd a b=0 ∧
      (run S depth i odd a).coarse.val=(run S depth i odd b).coarse.val ∧
      updated S depth i odd a b=(indexedFamily S depth).coboundary0 i.succ p := by sorry
