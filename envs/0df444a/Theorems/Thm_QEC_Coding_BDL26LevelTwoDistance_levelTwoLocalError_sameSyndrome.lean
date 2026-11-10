-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_sameSyndrome
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_sameSyndrome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:38:59.328816+00:00
-- url     : https://prove2.me/theorems/cd14b8fd-e78d-4c54-82b9-89ee4813d134
-- title:
--   BDL26 Level Two Distance: level Two Local Error same Syndrome
-- statement:
--   Concrete F17 two-local-error separation. The centers are independent:
--   first take the actual cocycle sum, project its owner-fibre support to at most
--   two RX coordinates, and construct a genuine RZ coboundary potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1238-L1256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1238-L1256

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_sameSyndrome (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second)
    (hsyn : tannerCoboundary1 (levelTwoPresentation S) first =
      tannerCoboundary1 (levelTwoPresentation S) second) :
    first + second ∈ (levelTwoChainComplex S).firstCoboundaryCheckCode.carrier := by sorry
