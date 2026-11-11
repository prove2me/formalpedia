-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_raw_local_edge_owner
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.raw_local_edge_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:42:09.903501+00:00
-- url     : https://prove2.me/theorems/34be56b8-6c9e-43ca-84b1-05a451de9771
-- title:
--   BDL26 RZPhysical Star Transport: raw local edge owner
-- statement:
--   Incident local edges have precisely the centre's old Z owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L169-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L169-L176

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
include odd

theorem QEC.Coding.BDL26RZPhysicalStarTransport.raw_local_edge_owner (z z' : (Old S depth i).Z)
    (e : ZDoubleCylinderEdge (Old S depth i) z S)
    (v : ZDoubleCylinderVertex (Old S depth i) z' S)
    (hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (.inl ⟨z,e⟩) ⟨z',v⟩=true) : z'=z := by sorry
