-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_local_edge_parent_none
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.local_edge_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:38:29.795446+00:00
-- url     : https://prove2.me/theorems/3a409b3d-df00-487b-a7c7-8c8902f6f35f
-- title:
--   BDL26 RXPhysical Star Transport: local edge parent none
-- statement:
--   Local-edge physical coordinates are genuinely unparented, unlike their X centres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L507-L510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L507-L510

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.local_edge_parent_none (x : XCoord S i)
    (e : DoubleCylinderEdge (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.q (upperQChart S depth i h (Sum.inl ⟨x,e⟩)))=none := by sorry
