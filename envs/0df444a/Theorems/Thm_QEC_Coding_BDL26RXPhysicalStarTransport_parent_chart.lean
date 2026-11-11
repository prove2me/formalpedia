-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_parent_chart
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.parent_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:03:49.762188+00:00
-- url     : https://prove2.me/theorems/b246633b-a7e9-4950-b6f5-3a9d90e091cc
-- title:
--   BDL26 RXPhysical Star Transport: parent chart
-- statement:
--   The existing partial graph parent of an X centre is computed, not supplied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L126-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L126-L130

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.parent_chart (x : XCoord S i)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.x (rxDegreeZeroEquiv S depth i h ⟨x,v⟩)) =
      some (Vertex.x x) := by sorry
