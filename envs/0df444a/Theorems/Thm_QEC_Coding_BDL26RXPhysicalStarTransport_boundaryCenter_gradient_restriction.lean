-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_gradient_restriction
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_gradient_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:23:26.626015+00:00
-- url     : https://prove2.me/theorems/9ceb2bb4-8cd5-4b78-8157-b96a1769ec23
-- title:
--   BDL26 RXPhysical Star Transport: boundary Center gradient restriction
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the boundary Center gradient restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L438-L442
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L438-L442

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_gradient_restriction (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x)
      (gradient S depth i (boundaryCenter S depth i h x))=boundaryGradient S depth i h x := by sorry
