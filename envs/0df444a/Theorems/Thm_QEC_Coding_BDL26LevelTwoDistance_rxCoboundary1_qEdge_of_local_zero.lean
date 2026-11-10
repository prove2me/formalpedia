-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rxCoboundary1_qEdge_of_local_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.rxCoboundary1_qEdge_of_local_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:49:05.223199+00:00
-- url     : https://prove2.me/theorems/78ea32e2-3093-45ad-bf73-a407f38afeb1
-- title:
--   BDL26 Level Two Distance: rx Coboundary1 q Edge of local zero
-- statement:
--   After the actual X-edge coordinates vanish, a Q-edge syndrome is the
--   sum of its two physical Q endpoint values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1086-L1103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1086-L1103

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

theorem QEC.Coding.BDL26LevelTwoDistance.rxCoboundary1_qEdge_of_local_zero (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RX1 P S))
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0)
    (q : P.Q) (edge : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S word (Sum.inl (Sum.inr ⟨q, edge⟩)) =
      word (Sum.inr ⟨q, qDoubleCylinderEdgeStart P q S edge⟩) +
        word (Sum.inr ⟨q, qDoubleCylinderEdgeEnd P q S edge⟩) := by sorry
