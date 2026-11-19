-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_repeated_input
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.repeated_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:50:00.283463+00:00
-- url     : https://prove2.me/theorems/72337f96-766e-4ace-9aaa-52d5e3fb72bd
-- title:
--   BDL26 Level Two Local Branch Endpoint: repeated input
-- statement:
--   Identical deterministic outputs cancel even at a NONZERO input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L529-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L529-L531

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.repeated_input (S : OddScale) (s : Syndrome S) :
    boundary S (0 : Potential S)=(0 : Error S)+D S s+D S s := by sorry
