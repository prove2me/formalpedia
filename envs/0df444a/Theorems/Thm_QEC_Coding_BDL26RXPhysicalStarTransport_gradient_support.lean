-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_gradient_support
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.gradient_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:12:26.198063+00:00
-- url     : https://prove2.me/theorems/404a80a4-c5a8-428e-b8b9-92278e33a437
-- title:
--   BDL26 RXPhysical Star Transport: gradient support
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the gradient support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L393-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L393-L396

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.gradient_support (u : FamilyX S depth i.succ) :
    hammingSupport (gradient S depth i u)=upperStar S depth i u := by sorry
