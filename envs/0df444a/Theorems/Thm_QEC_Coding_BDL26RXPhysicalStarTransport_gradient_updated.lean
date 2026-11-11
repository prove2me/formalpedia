-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_gradient_updated
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.gradient_updated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:14:08.010403+00:00
-- url     : https://prove2.me/theorems/7ff735c5-4a55-46d5-a23f-5b8304cd5e97
-- title:
--   BDL26 RXPhysical Star Transport: gradient updated
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the gradient updated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L415-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L415-L418

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.gradient_updated (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    updated S depth i h a (a+gradient S depth i u)=gradient S depth i u := by sorry
