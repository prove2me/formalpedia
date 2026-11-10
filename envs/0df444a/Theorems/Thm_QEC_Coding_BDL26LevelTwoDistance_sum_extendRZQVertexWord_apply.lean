-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_sum_extendRZQVertexWord_apply
-- name    : QEC.Coding.BDL26LevelTwoDistance.sum_extendRZQVertexWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:31:12.743168+00:00
-- url     : https://prove2.me/theorems/6b8d4633-a3a2-4f8a-a132-0a5022f06a2d
-- title:
--   BDL26 Level Two Distance: sum extend RZQVertex Word apply
-- statement:
--   All embedded physical Q restrictions reassemble their Q coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L688-L699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L688-L699

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

theorem QEC.Coding.BDL26LevelTwoDistance.sum_extendRZQVertexWord_apply (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) (q : P.Q)
    (vertex : QDoubleCylinderVertex (transposePresentation P) q S) :
    (∑ other : P.Q, extendRZQVertexWord P S other
      (fun v => word (Sum.inr ⟨other, v⟩))) (Sum.inr ⟨q, vertex⟩) =
        word (Sum.inr ⟨q, vertex⟩) := by sorry
