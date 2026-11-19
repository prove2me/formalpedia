-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_edge_parity_other
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_parity_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:49:12.857283+00:00
-- url     : https://prove2.me/theorems/1a7eddb0-8a71-456b-b5d7-9b7d5a0f4f08
-- title:
--   BDL26 Level Two Local Branch Endpoint: edge parity other
-- statement:
--   No Q label other than the actual Q-edge's own label occurs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L226-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L226-L238

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_parity_other (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h) (r : (P S).Q) (hr : r≠q) :
    parity S h r=0 := by sorry
