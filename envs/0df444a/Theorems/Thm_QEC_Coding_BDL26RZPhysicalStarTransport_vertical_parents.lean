-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_vertical_parents
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.vertical_parents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:41:31.447192+00:00
-- url     : https://prove2.me/theorems/01508f08-3f24-4c34-bbaa-70587cf8b33f
-- title:
--   BDL26 RZPhysical Star Transport: vertical parents
-- statement:
--   An actual incidence example with parented centre and unparented Q coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L442-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L442-L449

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.vertical_parents (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    (state S (i.val+1)).presentation.qz (verticalPhysical S depth i odd z v)
      (verticalCentre S depth i odd z v)=true ∧
    parent S (i.val+1) (Vertex.q (verticalPhysical S depth i odd z v))=none ∧
    parent S (i.val+1) (Vertex.z (verticalCentre S depth i odd z v))=some (Vertex.z z) := by sorry
