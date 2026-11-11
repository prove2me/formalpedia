-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_neighbors_parent
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.neighbors_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:02:56.665198+00:00
-- url     : https://prove2.me/theorems/d9d33623-ab14-4a6e-a63e-25877fdb00c0
-- title:
--   BDL26 RXPhysical Star Transport: neighbors parent
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the neighbors parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L162-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L162-L165

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.neighbors_parent (x : XCoord S i) :
    BDL26RXFiniteBlockTransport.neighbors S depth i {x} (incidentQ S depth i x)=
      physicalXStar (state S i.val).presentation x := by sorry
