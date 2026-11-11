-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_self_zero_potential
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.self_zero_potential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:09:32.770893+00:00
-- url     : https://prove2.me/theorems/f5e399d8-b4e0-45da-828e-4b9a20bb9117
-- title:
--   BDL26 RZPhysical XStar Transport: self zero potential
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the self zero potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L577-L583
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L577-L583

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_self_zero_potential

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.self_zero_potential (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a a 0 := by sorry
