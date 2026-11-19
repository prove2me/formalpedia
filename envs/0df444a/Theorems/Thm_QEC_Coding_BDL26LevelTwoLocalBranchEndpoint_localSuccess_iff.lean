-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSuccess_iff
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:49:06.710164+00:00
-- url     : https://prove2.me/theorems/39624e2a-8744-4c14-bf13-06b7be60b1fd
-- title:
--   BDL26 Level Two Local Branch Endpoint: local Success iff
-- statement:
--   Exact soundness/completeness on ALL raw physical syndrome words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L138-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L138-L151

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.localSuccess_iff (S : OddScale) (t : Syndrome S) :
    localSuccess S t ↔ ∃ e : Error S, levelTwoLocalError S e ∧ delta S e=t := by sorry
