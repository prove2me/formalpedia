-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzQEdge_coboundary_apply_q
-- name    : QEC.Coding.BDL26LevelTwoDistance.rzQEdge_coboundary_apply_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:51.627723+00:00
-- url     : https://prove2.me/theorems/7b607e04-9257-4786-b378-6cdba36d4f56
-- title:
--   BDL26 Level Two Distance: rz QEdge coboundary apply q
-- statement:
--   Evaluate an embedded Q-edge boundary on a physical Q-block coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L657-L670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L657-L670

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

theorem QEC.Coding.BDL26LevelTwoDistance.rzQEdge_coboundary_apply_q (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (q other : P.Q)
    (edges : Word Field (QDoubleCylinderEdge (transposePresentation P) q S))
    (vertex : QDoubleCylinderVertex (transposePresentation P) other S) :
    rzCoboundary0 P A4 S (extendRZQEdgeWord P S q edges) (Sum.inr ⟨other, vertex⟩) =
      extendRZQVertexWord P S q
        (qDoubleCylinderBoundary1 (transposePresentation P) q S edges)
        (Sum.inr ⟨other, vertex⟩) := by sorry
