-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_localLift_edge_same
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_edge_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:46:58.269589+00:00
-- url     : https://prove2.me/theorems/34e3961b-acdd-4897-a902-391de0296b2f
-- title:
--   BDL26 Level Two Old XStar Endpoint: local Lift edge same
-- statement:
--   The BDL26 Level Two Old XStar Endpoint construction uses the local Lift edge same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L137-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L137-L144

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_edge_same (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) (e : DoubleCylinderEdge Seed x S) :
    rxCoboundary0 Seed S (localLift S x f) (Sum.inl ⟨x,e⟩)=
      wordLinearMapTranspose (rxCx Seed x S).boundary1 f e := by sorry
