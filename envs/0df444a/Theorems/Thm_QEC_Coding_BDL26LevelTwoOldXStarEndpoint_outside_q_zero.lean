-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_outside_q_zero
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outside_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:49:54.378948+00:00
-- url     : https://prove2.me/theorems/16dd656b-7bd4-41b3-9441-621bf857b458
-- title:
--   BDL26 Level Two Old XStar Endpoint: outside q zero
-- statement:
--   Three literal vertices kill the remaining two-coordinate spill at half1 too.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L214-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L214-L249

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outside_q_zero (S : OddScale) (x : BaseX) (w : W1 S)
    (hc : rxCoboundary1 Seed S w=0)
    (hx : ∀ y e, w (Sum.inl ⟨y,e⟩)=0) (a b : RX1 Seed S)
    (hw : ∀ r, w r≠0 → r∈Neighborhood S x ∨ r=a ∨ r=b)
    (q : BaseQubit) (hq : Seed.xq x q≠true)
    (v : QDoubleCylinderVertex Seed q S) : w (Sum.inr ⟨q,v⟩)=0 := by sorry
