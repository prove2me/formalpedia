-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_add_qParity_two_coordinates
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_add_qParity_two_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:33:46.821555+00:00
-- url     : https://prove2.me/theorems/9c231961-fb47-4198-ab8a-a3337b56ca4e
-- title:
--   BDL26 Level Two Distance: level Two Local Error add q Parity two coordinates
-- statement:
--   Convert the actual owner-label support conclusion to two coordinate
--   labels without assuming that either local center is a Q vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1007-L1018
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1007-L1018

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_add_qParity_two_coordinates (S : OddScale)
    (defaultQ : (levelOnePresentation S).Q)
    (first second : Word Field (levelTwoPresentation S).Q)
    (hfirst : levelTwoLocalError S first) (hsecond : levelTwoLocalError S second) :
    ∃ a b : (levelOnePresentation S).Q,
      ∀ q, rzQParity (levelOnePresentation S) S (first + second) q ≠ 0 → q = a ∨ q = b := by sorry
