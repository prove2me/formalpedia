-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_edge_Q_nonzero
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_Q_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:49:38.695294+00:00
-- url     : https://prove2.me/theorems/ef557f6a-f471-4202-a811-68f58f36aa05
-- title:
--   BDL26 Level Two Local Branch Endpoint: edge Q nonzero
-- statement:
--   The only possible Q coefficients are the two actual edge endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L278-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L278-L292

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_Q_nonzero (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h)
    (v : QDoubleCylinderVertex (transposePresentation (P S)) q S)
    (hv : h (.inr ⟨q,v⟩)≠0) :
    v=qDoubleCylinderEdgeStart (transposePresentation (P S)) q S e ∨
      v=qDoubleCylinderEdgeEnd (transposePresentation (P S)) q S e := by sorry
