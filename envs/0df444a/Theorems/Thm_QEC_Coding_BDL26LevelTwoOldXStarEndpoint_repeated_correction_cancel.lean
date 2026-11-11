-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_repeated_correction_cancel
-- name    : QEC.Coding.BDL26LevelTwoOldXStarEndpoint.repeated_correction_cancel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:39:48.770751+00:00
-- url     : https://prove2.me/theorems/d9397a6f-b530-4636-a6ec-3379b93c8e94
-- title:
--   BDL26 Level Two Old XStar Endpoint: repeated correction cancel
-- statement:
--   Repeated nonzero input cancellation uses only determinism, not D-linearity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L681-L682
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoOldXStarEndpoint.lean#L681-L682

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
attribute [local instance] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldXActualQFintype

theorem QEC.Coding.BDL26LevelTwoOldXStarEndpoint.repeated_correction_cancel (S : OddScale) (s : Word F (C S).Z) :
    decode S s+decode S s=0 := by sorry
