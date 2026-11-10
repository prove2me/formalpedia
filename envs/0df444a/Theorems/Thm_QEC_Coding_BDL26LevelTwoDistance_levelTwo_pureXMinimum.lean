-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwo_pureXMinimum
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwo_pureXMinimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:37.854104+00:00
-- url     : https://prove2.me/theorems/b3e5c393-4f1d-4ea1-83d3-9cd4aa9c4146
-- title:
--   BDL26 Level Two Distance: level Two pure XMinimum
-- statement:
--   The BDL26 Level Two Distance construction uses the level Two pure XMinimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L525-L527
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L525-L527

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwo_pureXMinimum (S : OddScale) :
    PureXLogicalMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (levelTwoXDistance S) := by sorry
