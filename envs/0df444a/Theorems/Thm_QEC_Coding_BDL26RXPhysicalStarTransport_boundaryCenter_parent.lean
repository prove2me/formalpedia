-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_boundaryCenter_parent
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:03:57.00505+00:00
-- url     : https://prove2.me/theorems/686a6539-2ce1-4c2f-97d5-f7dc8ba6e654
-- title:
--   BDL26 RXPhysical Star Transport: boundary Center parent
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the boundary Center parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L429-L430
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L429-L430

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.boundaryCenter_parent (x : XCoord S i) :
    parentX S depth i h (boundaryCenter S depth i h x)=x := by sorry
