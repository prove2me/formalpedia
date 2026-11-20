-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_localSearch_none_iff
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.localSearch_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:50:42.906639+00:00
-- url     : https://prove2.me/theorems/a969f9da-7a57-49ef-a52f-64ff6a78dd67
-- title:
--   BDL26 Level Two Local Branch Endpoint: local Search none iff
-- statement:
--   None excludes exactly the original owner-local preimages, not logical errors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L160-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L160-L164

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.localSearch_none_iff (S : OddScale) (t : Syndrome S) :
    localSearch S t=none ↔ ¬∃ e : Error S, levelTwoLocalError S e ∧ delta S e=t := by sorry
