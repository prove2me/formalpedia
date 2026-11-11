-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_gradient_coarse_zero
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.gradient_coarse_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:41:59.798195+00:00
-- url     : https://prove2.me/theorems/0c1687fe-b8ec-4207-b28a-69b67ca42535
-- title:
--   BDL26 RZPhysical XStar Transport: gradient coarse zero
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the gradient coarse zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L473-L475
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L473-L475

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_gradient_coarse_zero

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.gradient_coarse_zero (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    (run S depth i odd a).coarse.val+(run S depth i odd (a+gradient S depth i u)).coarse.val=0 := by sorry
