-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_localLift_other
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:29:44.940226+00:00
-- url     : https://prove2.me/theorems/f3bc3922-9af7-459d-9d1b-93ef4e179825
-- title:
--   BDL26 Level Two Old XStar Endpoint: local Lift other
-- statement:
--   The BDL26 Level Two Old XStar Endpoint construction uses the local Lift other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L130-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L130-L135

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

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.localLift_other (S : OddScale) (x y : BaseX) (hy : y≠x)
    (f : Word F (DoubleCylinderVertex Seed x S)) (v : DoubleCylinderVertex Seed y S) :
    localLift S x f ⟨y,v⟩=0 := by sorry
