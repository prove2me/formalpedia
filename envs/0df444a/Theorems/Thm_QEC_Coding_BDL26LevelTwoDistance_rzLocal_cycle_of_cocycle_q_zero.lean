-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzLocal_cycle_of_cocycle_q_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzLocal_cycle_of_cocycle_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:25.923916+00:00
-- url     : https://prove2.me/theorems/16bedbe2-69dc-4c19-a932-2d700b3897e5
-- title:
--   BDL26 Level Two Distance: rz Local cycle of cocycle q zero
-- statement:
--   A cocycle with no Q coordinates restricts to a cycle in every actual
--   Z cylinder. The proof uses the materialized global incidence map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L716-L742
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L716-L742

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzLocal_cycle_of_cocycle_q_zero (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hc : rzCoboundary1 P A4 S word = 0)
    (hq : ∀ q vertex, word (Sum.inr ⟨q, vertex⟩) = 0) (z : P.Z) :
    doubleCylinderBoundary1 (transposePresentation P) z S
      (fun edge => word (Sum.inl ⟨z, edge⟩)) = 0 := by sorry
