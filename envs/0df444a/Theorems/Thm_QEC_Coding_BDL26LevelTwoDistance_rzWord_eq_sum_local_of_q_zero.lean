-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzWord_eq_sum_local_of_q_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzWord_eq_sum_local_of_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:28:15.044201+00:00
-- url     : https://prove2.me/theorems/d27d8c6d-a8f9-412a-85f4-2a4a18fbb6f7
-- title:
--   BDL26 Level Two Distance: rz Word eq sum local of q zero
-- statement:
--   A word with no physical Q coordinates is exactly its sum of local Z
--   restrictions, retaining all local edge coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L703-L712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L703-L712

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzWord_eq_sum_local_of_q_zero (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S))
    (hq : ∀ q vertex, word (Sum.inr ⟨q, vertex⟩) = 0) :
    word = ∑ z : P.Z, extendZEdgeWord P S z
      (fun edge => word (Sum.inl ⟨z, edge⟩)) := by sorry
