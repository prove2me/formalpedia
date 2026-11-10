-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwo_pureZMinimum
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwo_pureZMinimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:47:09.010471+00:00
-- url     : https://prove2.me/theorems/dedb9647-7d93-4587-ad3e-df6ff808c8ed
-- title:
--   BDL26 Level Two Distance: level Two pure ZMinimum
-- statement:
--   The BDL26 Level Two Distance construction uses the level Two pure ZMinimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L529-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L529-L531

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwo_pureZMinimum (S : OddScale) :
    PureZLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (levelTwoZDistance S) := by sorry
