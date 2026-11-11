-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_localLift_edge_other
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_edge_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:48:07.346906+00:00
-- url     : https://prove2.me/theorems/411479f0-32b1-40fc-acae-e99a3d695ed9
-- title:
--   BDL26 Level Two Old XStar Endpoint: local Lift edge other
-- statement:
--   The BDL26 Level Two Old XStar Endpoint construction uses the local Lift edge other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L146-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L146-L159

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_edge_other (S : OddScale) (x y : BaseX) (hy : y≠x)
    (f : Word F (DoubleCylinderVertex Seed x S)) (e : DoubleCylinderEdge Seed y S) :
    rxCoboundary0 Seed S (localLift S x f) (Sum.inl ⟨y,e⟩)=0 := by sorry
