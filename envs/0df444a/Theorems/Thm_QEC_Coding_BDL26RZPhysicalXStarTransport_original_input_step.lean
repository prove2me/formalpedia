-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_original_input_step
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.original_input_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:43:47.024349+00:00
-- url     : https://prove2.me/theorems/28ae20db-e942-4c59-98ae-f0d58c81f301
-- title:
--   BDL26 RZPhysical XStar Transport: original input step
-- statement:
--   Adjacent stored inputs use precisely the previous selected coarse output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L662-L666
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L662-L666

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.original_input_step (S : OddScale) (n : Nat) (s : TopInput S n) (k : StepIndex n) :
    BDL26CanonicalHistoryMarks.inputAt S n s k.castSucc=
      (BDL26CanonicalHistoryMarks.outputAt S n s k).coarse := by sorry
