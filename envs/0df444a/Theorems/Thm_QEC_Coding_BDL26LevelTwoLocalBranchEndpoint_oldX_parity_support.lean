-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoLocalBranchEndpoint_oldX_parity_support
-- name    : QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.oldX_parity_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:54:59.659805+00:00
-- url     : https://prove2.me/theorems/2917d4e9-0b4d-4ce8-8131-2fa85c5af489
-- title:
--   BDL26 Level Two Local Branch Endpoint: old X parity support
-- statement:
--   Actual old-X copies retain the FULL preceding incidence-star support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L241-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoLocalBranchEndpoint.lean#L241-L252

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

theorem QEC.Coding.BDL26LevelTwoLocalBranchEndpoint.oldX_parity_support (S : OddScale) (x : (P S).X) (copy : BDL26FiniteTannerSquare.Two)
    (h : Error S) (hh : supported S (.inr (x,copy)) h) (q : (P S).Q)
    (hq : parity S h q≠0) :
    q ∈ BDL26RXPhysicalStarTransport.physicalXStar (P S) x := by sorry
