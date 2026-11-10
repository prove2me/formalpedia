-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rxCocycle_q_constant_of_local_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.rxCocycle_q_constant_of_local_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:34:03.676686+00:00
-- url     : https://prove2.me/theorems/726ca3e8-cd13-4d12-836c-91d89893a959
-- title:
--   BDL26 Level Two Distance: rx Cocycle q constant of local zero
-- statement:
--   An actual RX cocycle with zero X-edge coordinates is constant on every
--   connected Q cylinder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1107-L1120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1107-L1120

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

theorem QEC.Coding.BDL26LevelTwoDistance.rxCocycle_q_constant_of_local_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RX1 P S))
    (hc : rxCoboundary1 P S word = 0)
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S) :
    word (Sum.inr ⟨q, vertex⟩) = word (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩) := by sorry
