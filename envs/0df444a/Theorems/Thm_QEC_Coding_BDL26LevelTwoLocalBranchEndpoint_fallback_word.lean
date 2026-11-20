-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_fallback_word
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.fallback_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:55:47.582328+00:00
-- url     : https://prove2.me/theorems/f8bfa221-ef5f-4e6c-b3ec-ab2a1fe0bb73
-- title:
--   BDL26 Level Two Local Branch Endpoint: fallback word
-- statement:
--   A failed first search takes the actual unfiltered branch with its default.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L167-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L167-L172

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.fallback_word (S : OddScale) (t : Syndrome S) (hn : localSearch S t=none) :
    D S t=BDL26LevelTwoDecoder.toActualError S ((globalSearch S t).getD 0) := by sorry
