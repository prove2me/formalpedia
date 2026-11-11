-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_outsideMask_read
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:29:35.506808+00:00
-- url     : https://prove2.me/theorems/fe490f61-5b2a-46a0-bc72-4dccc161a401
-- title:
--   BDL26 Level Two Old XStar Endpoint: outside Mask read
-- statement:
--   The BDL26 Level Two Old XStar Endpoint construction uses the outside Mask read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L66-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L66-L71

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.outsideMask_read (S : OddScale) (y : BaseX) (w : W1 S)
    (e : DoubleCylinderEdge Seed y S) :
    outsideMask S y w (Sum.inl ⟨y,e⟩)=w (Sum.inl ⟨y,e⟩) := by sorry
