-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_block_star_parent
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.block_star_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:02:56.306474+00:00
-- url     : https://prove2.me/theorems/019ae925-edad-4103-acbd-d1e8ee3aff82
-- title:
--   BDL26 RXPhysical Star Transport: block star parent
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the block star parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L167-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L167-L173

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.block_star_parent (x : XCoord S i) :
    BDL26RXFiniteBlockTransport.star S depth i h {x} (incidentQ S depth i x)=
      star1 S depth i h x := by sorry
