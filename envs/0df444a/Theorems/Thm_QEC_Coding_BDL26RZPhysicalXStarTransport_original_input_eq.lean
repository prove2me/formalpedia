-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_original_input_eq
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.original_input_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:25:56.207592+00:00
-- url     : https://prove2.me/theorems/7acadb07-ceb5-4823-bf1c-e4b9a589d355
-- title:
--   BDL26 RZPhysical XStar Transport: original input eq
-- statement:
--   The original unique stored input equals the proved traversal of that SAME history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L642-L659
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L642-L659

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
open BDL26HistorySyndromeSensitivity

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.original_input_eq (S : OddScale) (n : Nat) (s : TopInput S n) (a : LevelIndex n) :
    BDL26CanonicalHistoryMarks.inputAt S n s a=actualInputs S n s a := by sorry
