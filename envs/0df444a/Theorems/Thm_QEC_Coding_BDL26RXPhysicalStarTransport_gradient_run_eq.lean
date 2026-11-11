-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_gradient_run_eq
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.gradient_run_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:04:52.974209+00:00
-- url     : https://prove2.me/theorems/ca66a692-5e5b-4c2d-988f-9f3a5d47358d
-- title:
--   BDL26 RXPhysical Star Transport: gradient run eq
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the gradient run eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L407-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L407-L413

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.gradient_run_eq (u : FamilyX S depth i.succ) (a : Upper S depth i) :
    run S depth i h (a+gradient S depth i u)=run S depth i h a := by sorry
