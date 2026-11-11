-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_gradient_nonzero
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_gradient_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:35:36.027729+00:00
-- url     : https://prove2.me/theorems/673051de-6808-41a5-a01c-2df5de1823eb
-- title:
--   BDL26 RXPhysical Star Transport: boundary Center gradient nonzero
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the boundary Center gradient nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L444-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L444-L449

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_gradient_nonzero (x : XCoord S i) :
    gradient S depth i (boundaryCenter S depth i h x)≠0 := by sorry
