-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_qCoordinateOfOwner_of_eq
-- name    : QEC.Coding.BDL26LevelTwoDistance.qCoordinateOfOwner_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:33:06.997973+00:00
-- url     : https://prove2.me/theorems/ec7f5049-e3fb-403c-81b6-ffde183d5d02
-- title:
--   BDL26 Level Two Distance: q Coordinate Of Owner of eq
-- statement:
--   The BDL26 Level Two Distance construction uses the q Coordinate Of Owner of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L999-L1003
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L999-L1003

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph

theorem QEC.Coding.BDL26LevelTwoDistance.qCoordinateOfOwner_of_eq (P : TannerSquarePresentation) (defaultQ q : P.Q)
    (owner : Vertex P) (h : Vertex.q q = owner) :
    q = qCoordinateOfOwner P defaultQ owner := by sorry
