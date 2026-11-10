-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rxCocycle_two_support_eq_zero_of_local_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.rxCocycle_two_support_eq_zero_of_local_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:48:53.682372+00:00
-- url     : https://prove2.me/theorems/53d01ba2-f5d9-4e73-9274-a597ab4dc027
-- title:
--   BDL26 Level Two Distance: rx Cocycle two support eq zero of local zero
-- statement:
--   Three explicit distinct vertices in each Q cylinder rule out a nonzero
--   constant restriction of a word supported on at most two physical coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1130-L1159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1130-L1159

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

theorem QEC.Coding.BDL26LevelTwoDistance.rxCocycle_two_support_eq_zero_of_local_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RX1 P S))
    (hc : rxCoboundary1 P S word = 0)
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0)
    (a b : RX1 P S) (hsupport : ∀ c, word c ≠ 0 → c = a ∨ c = b) : word = 0 := by sorry
