-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_physical_star_subset
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.physical_star_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:45:45.950252+00:00
-- url     : https://prove2.me/theorems/800cd381-2611-48b4-a4dd-81959211816c
-- title:
--   BDL26 Level Two Old XStar Endpoint: physical star subset
-- statement:
--   Every actual first-level physical X star lies in the declared neighborhood.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L49-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L49-L58

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.physical_star_subset (S : OddScale) (x : (P S).X) :
    BDL26RXPhysicalStarTransport.physicalXStar (P S) x ⊆ Neighborhood S x.1 := by sorry
