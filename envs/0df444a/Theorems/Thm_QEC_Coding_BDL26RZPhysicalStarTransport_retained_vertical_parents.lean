-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_retained_vertical_parents
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.retained_vertical_parents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:29:29.714098+00:00
-- url     : https://prove2.me/theorems/2a1a597b-5c18-4ea4-b28e-9b274c26af67
-- title:
--   BDL26 RZPhysical Star Transport: retained vertical parents
-- statement:
--   No nonemptiness or incidence witness is supplied for this actual vertical example.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L470-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L470-L479

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.retained_vertical_parents :
    (state S (i.val+1)).presentation.qz
      (verticalPhysical S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i))
      (verticalCentre S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i))=true ∧
    parent S (i.val+1) (Vertex.q
      (verticalPhysical S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i)))=none ∧
    parent S (i.val+1) (Vertex.z
      (verticalCentre S depth i odd (retainedZ S depth i) (retainedBoundaryVertex S depth i)))=
        some (Vertex.z (retainedZ S depth i)) := by sorry
