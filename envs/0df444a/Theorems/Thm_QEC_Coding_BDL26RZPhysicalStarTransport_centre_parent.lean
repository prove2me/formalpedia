-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_centre_parent
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.centre_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:19:52.822856+00:00
-- url     : https://prove2.me/theorems/2dbd5f74-91b3-4c57-a5df-eb710f19a2b2
-- title:
--   BDL26 RZPhysical Star Transport: centre parent
-- statement:
--   Whole-Vertex transport computes the actual existing partial parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L215-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L215-L220

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.centre_parent (z : (Old S depth i).Z)
    (v : ZDoubleCylinderVertex (Old S depth i) z S) :
    parent S (i.val+1) (Vertex.z (upperZChart S depth i odd ⟨z,v⟩))=some (Vertex.z z) := by sorry
