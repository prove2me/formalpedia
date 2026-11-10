-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_iff_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:18.178397+00:00
-- url     : https://prove2.me/theorems/1038e0b9-3d03-4535-8e40-9262b1978fdb
-- title:
--   BDL26 Level Two Distance: level Two Local Error iff owner
-- statement:
--   The selected predicate is exactly the physical coordinate owner fibre,
--   with no identification of a graph radius with Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L562-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L562-L570

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_iff_owner (S : OddScale)
    (error : Word Field (levelTwoPresentation S).Q) :
    levelTwoLocalError S error ↔
      ∃ center : Vertex (levelOnePresentation S), ∀ coordinate,
        error coordinate ≠ 0 →
          BDL26ReplacementSupport.rzCorrectionOwner (levelOnePresentation S) S coordinate = center := by sorry
