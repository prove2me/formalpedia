-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_outside_edges_zero
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outside_edges_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T16:47:04.01855+00:00
-- url     : https://prove2.me/theorems/7b2a3357-cdf1-485a-9b2b-d3d39355d55b
-- title:
--   BDL26 Level Two Old XStar Endpoint: outside edges zero
-- statement:
--   Nonzero distinct actual seed columns kill each outside cylinder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L102-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L102-L116

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outside_edges_zero (S : OddScale) (x y : BaseX) (hy : y≠x)
    (w : W1 S) (hc : rxCoboundary1 Seed S w=0) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b)
    (e : DoubleCylinderEdge Seed y S) : w (Sum.inl ⟨y,e⟩)=0 := by sorry
