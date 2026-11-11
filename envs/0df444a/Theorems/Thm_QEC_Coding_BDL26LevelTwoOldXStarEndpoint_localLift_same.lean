-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_localLift_same
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:28:57.436743+00:00
-- url     : https://prove2.me/theorems/9fe675ad-7dd4-4dd0-9784-6a45219e56de
-- title:
--   BDL26 Level Two Old XStar Endpoint: local Lift same
-- statement:
--   The BDL26 Level Two Old XStar Endpoint construction uses the local Lift same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L123-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L123-L128

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_same (S : OddScale) (x : BaseX)
    (f : Word F (DoubleCylinderVertex Seed x S)) (v : DoubleCylinderVertex Seed x S) :
    localLift S x f ⟨x,v⟩=f v := by sorry
