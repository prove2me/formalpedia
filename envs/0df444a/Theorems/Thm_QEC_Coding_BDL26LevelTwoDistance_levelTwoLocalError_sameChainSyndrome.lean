-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_sameChainSyndrome
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_sameChainSyndrome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:26:30.935897+00:00
-- url     : https://prove2.me/theorems/029d4709-eab2-4d5b-b6a0-55a5489a5244
-- title:
--   BDL26 Level Two Distance: level Two Local Error same Chain Syndrome
-- statement:
--   The same separation stated directly with the concrete chain complex's
--   syndrome map, for callers using the M3 code interface.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1260-L1267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1260-L1267

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_sameChainSyndrome (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second)
    (hsyn : wordLinearMapTranspose (levelTwoChainComplex S).boundary2 first =
      wordLinearMapTranspose (levelTwoChainComplex S).boundary2 second) :
    first + second ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by sorry
