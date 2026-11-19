-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_edge_endpoint
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_endpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:51:37.094065+00:00
-- url     : https://prove2.me/theorems/c5d4e2bc-8f30-46bb-aad6-d6d832e14d01
-- title:
--   BDL26 Level Two Local Branch Endpoint: edge endpoint
-- statement:
--   Arbitrary endpoint values and ALL neighbouring Z bits, not just one owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L430-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L430-L434

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.edge_endpoint (S : OddScale) (q : (P S).Q)
    (e : QDoubleCylinderEdge (transposePresentation (P S)) q S) (h : Error S)
    (hh : supported S (.inl (.inr ⟨q,e⟩)) h) (hb : localSuccess S (delta S h)) :
    ∃ p : Potential S, boundary S p=h+D S 0+D S (delta S h) := by sorry
