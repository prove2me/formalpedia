-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_of_other_owner
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzQParity_zero_of_other_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:33:29.157728+00:00
-- url     : https://prove2.me/theorems/1e20a2af-5b8c-406e-8f85-d8f5d58d7e34
-- title:
--   BDL26 Level Two Distance: rz QParity zero of other owner
-- statement:
--   A physical owner-local word has no Q parity outside its own Q label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L805-L816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L805-L816

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzQParity_zero_of_other_owner (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) (owner : Vertex P)
    (howner : ∀ coordinate, word coordinate ≠ 0 →
      BDL26ReplacementSupport.rzCorrectionOwner P S coordinate = owner)
    (q : P.Q) (hne : Vertex.q q ≠ owner) : rzQParity P S word q = 0 := by sorry
