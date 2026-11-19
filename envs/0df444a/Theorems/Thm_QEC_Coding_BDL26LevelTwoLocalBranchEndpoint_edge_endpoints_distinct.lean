-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_edge_endpoints_distinct
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_endpoints_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:50:13.431772+00:00
-- url     : https://prove2.me/theorems/a33e8953-3fab-4ff5-b444-8919e93ce27b
-- title:
--   BDL26 Level Two Local Branch Endpoint: edge endpoints distinct
-- statement:
--   Proved locally from tagged actual vertices, including half=1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L255-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L255-L275

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoLocalBranchEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoLocalBranchEndpoint
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26LevelTwoCode
open BDL26LevelTwoDistance BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open scoped BigOperators
open scoped Classical

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_endpoints_distinct (S : OddScale) (q : (P S).Q)
    (edge : QDoubleCylinderEdge (transposePresentation (P S)) q S) :
    qDoubleCylinderEdgeStart (transposePresentation (P S)) q S edge ≠
      qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S edge := by sorry
