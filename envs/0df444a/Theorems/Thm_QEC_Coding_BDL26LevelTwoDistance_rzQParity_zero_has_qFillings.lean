-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQParity_zero_has_qFillings
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzQParity_zero_has_qFillings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:29.943234+00:00
-- url     : https://prove2.me/theorems/959fb1e5-4a19-456a-978e-08e05af70a89
-- title:
--   BDL26 Level Two Distance: rz QParity zero has q Fillings
-- statement:
--   Each even physical Q block has a concrete Q-edge filling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L673-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L673-L685

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzQParity_zero_has_qFillings (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RZQ P S))
    (hparity : rzQParity P S word = 0) :
    ∀ q : P.Q, ∃ edges : Word Field (QDoubleCylinderEdge (transposePresentation P) q S),
      qDoubleCylinderBoundary1 (transposePresentation P) q S edges =
        fun vertex => word (Sum.inr ⟨q, vertex⟩) := by sorry
