-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_seedRX_two_support_cocycle_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.seedRX_two_support_cocycle_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:48:38.328938+00:00
-- url     : https://prove2.me/theorems/22a9f3ca-dd50-454d-89ef-0196ea367c33
-- title:
--   BDL26 Level Two Distance: seed RX two support cocycle zero
-- statement:
--   A two-coordinate-supported cocycle in the actual seed RX replacement
--   vanishes. Local face incidence kills X edges; connected Q cylinders then
--   have constant restrictions, which three distinct physical vertices kill.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1197-L1221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1197-L1221

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

theorem QEC.Coding.BDL26LevelTwoDistance.seedRX_two_support_cocycle_zero (S : OddScale)
    (word : Word Field (RX1 baseTannerSquarePresentation S))
    (hc : rxCoboundary1 baseTannerSquarePresentation S word = 0)
    (a b : RX1 baseTannerSquarePresentation S)
    (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by sorry
