-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_nextOutput_run
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:44:14.209806+00:00
-- url     : https://prove2.me/theorems/fe9a67b1-6190-40f2-98c9-1d30d5a116d8
-- title:
--   BDL26 RZPhysical XStar Transport: next Output run
-- statement:
--   The reconstructed representatives give the SAME full canonical outputs, not only the same corrections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L729-L740
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L729-L740

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_run (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    BDL26RXErrorPullback.run S (2*j+4) (rxStep j) (rxStep_even j) (firstRepresentative S j a)=nextOutput S j a ∧
    BDL26RXErrorPullback.run S (2*j+4) (rxStep j) (rxStep_even j) (secondRepresentative S j a b)=nextOutput S j b := by sorry
