-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelOne_two_support_cocycle_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.levelOne_two_support_cocycle_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:33:56.946639+00:00
-- url     : https://prove2.me/theorems/2601f20d-18db-4c64-88cb-8c00da3fe544
-- title:
--   BDL26 Level Two Distance: level One two support cocycle zero
-- statement:
--   The coordinate statement is transported to the actual first-level
--   presentation incidence, with no alternate chain complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1225-L1233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1225-L1233

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

theorem QEC.Coding.BDL26LevelTwoDistance.levelOne_two_support_cocycle_zero (S : OddScale)
    (word : Word Field (levelOnePresentation S).Q)
    (hc : tannerCoboundary1 (levelOnePresentation S) word = 0)
    (a b : (levelOnePresentation S).Q)
    (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by sorry
