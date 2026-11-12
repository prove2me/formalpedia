-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_nextOutput_input
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:12:17.731514+00:00
-- url     : https://prove2.me/theorems/ddc2b865-a4da-4172-bec3-6fc9a15f186c
-- title:
--   BDL26 RZPhysical XStar Transport: next Output input
-- statement:
--   The next stored run's input is exactly the original first coarse input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L723-L726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L723-L726

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_input (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    (nextOutput S j a).input=(topOutput S j a).coarse := by sorry
