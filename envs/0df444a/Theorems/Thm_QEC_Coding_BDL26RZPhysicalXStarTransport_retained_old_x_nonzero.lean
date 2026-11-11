-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_retained_old_x_nonzero
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.retained_old_x_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:43:15.007201+00:00
-- url     : https://prove2.me/theorems/5f9266fc-92ad-4609-bced-487e4ca2a656
-- title:
--   BDL26 RZPhysical XStar Transport: retained old x nonzero
-- statement:
--   Internally retained-face incidence proves the lower closed word is actually nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L536-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L536-L547

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.retained_old_x_nonzero (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    lowerError S depth i odd a
      (a+gradient S depth i (upperXChart S depth i odd (.inr (retainedX S depth i,c))))≠0 := by sorry
