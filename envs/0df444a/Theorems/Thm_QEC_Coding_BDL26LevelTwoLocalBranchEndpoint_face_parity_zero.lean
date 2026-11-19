-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_face_parity_zero
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.face_parity_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:51:36.443662+00:00
-- url     : https://prove2.me/theorems/8fe0609b-1ded-45da-a3de-c9a0760322ca
-- title:
--   BDL26 Level Two Local Branch Endpoint: face parity zero
-- statement:
--   Complete Z-face star words have zero preceding-Q parity, with all Z bits kept.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L212-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L212-L223

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.face_parity_zero (S : OddScale) (z : (P S).Z)
    (f : ZDoubleCylinderFace (P S) z S) (h : Error S)
    (hh : supported S (.inl (.inl ⟨z,f⟩)) h) : parity S h=0 := by sorry
