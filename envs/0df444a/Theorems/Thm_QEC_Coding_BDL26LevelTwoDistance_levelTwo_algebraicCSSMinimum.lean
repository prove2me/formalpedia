-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwo_algebraicCSSMinimum
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwo_algebraicCSSMinimum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:25:39.144266+00:00
-- url     : https://prove2.me/theorems/91a3b66c-1ffb-4fa7-b03e-6f4cac97220d
-- title:
--   BDL26 Level Two Distance: level Two algebraic CSSMinimum
-- statement:
--   The combined finite CSS minimum is the minimum of the two attained
--   logical-sector minima. This is not an asymptotic lower-bound claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L535-L539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L535-L539

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwo_algebraicCSSMinimum (S : OddScale) :
    AlgebraicCSSMinimumDistance (levelTwoXCode S) (levelTwoZCode S)
      (min (levelTwoXDistance S) (levelTwoZDistance S)) := by sorry
