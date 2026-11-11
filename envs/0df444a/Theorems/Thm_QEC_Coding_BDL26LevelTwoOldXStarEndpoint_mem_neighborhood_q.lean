-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_mem_neighborhood_q
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.mem_neighborhood_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:29:06.425226+00:00
-- url     : https://prove2.me/theorems/48875759-cd44-405e-bc54-3f36a6f1043e
-- title:
--   BDL26 Level Two Old XStar Endpoint: mem neighborhood q
-- statement:
--   The BDL26 Level Two Old XStar Endpoint construction uses the mem neighborhood q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L44-L46

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.mem_neighborhood_q (S : OddScale) (x : BaseX) (q : BaseQubit)
    (v : QDoubleCylinderVertex Seed q S) :
    Sum.inr ⟨q,v⟩ ∈ Neighborhood S x ↔ Seed.xq x q=true := by sorry
