-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzCocycle_q_zero_is_coboundary
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzCocycle_q_zero_is_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:47:22.010273+00:00
-- url     : https://prove2.me/theorems/06549d56-a946-4470-b704-d2981ac87125
-- title:
--   BDL26 Level Two Distance: rz Cocycle q zero is coboundary
-- statement:
--   A cocycle entirely in Z-local edges has an actual global face potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L745-L762
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L745-L762

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzCocycle_q_zero_is_coboundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hc : rzCoboundary1 P A4 S word = 0)
    (hq : ∀ q vertex, word (Sum.inr ⟨q, vertex⟩) = 0) :
    ∃ potential : Word Field (RZX P S), rzCoboundary0 P A4 S potential = word := by sorry
