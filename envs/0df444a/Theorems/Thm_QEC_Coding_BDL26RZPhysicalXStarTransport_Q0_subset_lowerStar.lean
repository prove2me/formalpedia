-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_Q0_subset_lowerStar
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.Q0_subset_lowerStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:36:18.768615+00:00
-- url     : https://prove2.me/theorems/39d8fa26-379d-4859-8150-96de81f850cc
-- title:
--   BDL26 RZPhysical XStar Transport: Q0 subset lower Star
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the Q0 subset lower Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L260-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L260-L262

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.Q0_subset_lowerStar (u : FamilyX S depth i.succ) :
    Q0 S depth i odd u ⊆ BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) := by sorry
