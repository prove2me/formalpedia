-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_gradient_coarse_zero
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.gradient_coarse_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:14:22.906199+00:00
-- url     : https://prove2.me/theorems/ea3dc86e-db92-4ad8-9fb4-cf574a01fa5e
-- title:
--   BDL26 RXPhysical Star Transport: gradient coarse zero
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the gradient coarse zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L420-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L420-L423

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXPhysicalStarTransport.gradient_coarse_zero (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    (coarseSum S depth i h a (a+gradient S depth i u)).val=0 := by sorry
