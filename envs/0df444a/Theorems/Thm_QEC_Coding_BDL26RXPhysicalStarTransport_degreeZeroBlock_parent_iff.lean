-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_degreeZeroBlock_parent_iff
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.degreeZeroBlock_parent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:05:49.080196+00:00
-- url     : https://prove2.me/theorems/f1cab58c-4b24-4929-9a3d-49721f6ee57c
-- title:
--   BDL26 RXPhysical Star Transport: degree Zero Block parent iff
-- statement:
--   Only upper X coordinates are identified with this parent fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L138-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L138-L151

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.degreeZeroBlock_parent_iff (x : XCoord S i) (u : FamilyX S depth i.succ) :
    u ∈ degreeZeroBlock S depth i h x ↔
      parent S (i.val+1) (Vertex.x u)=some (Vertex.x x) := by sorry
