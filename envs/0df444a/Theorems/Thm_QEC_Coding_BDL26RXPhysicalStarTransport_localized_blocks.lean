-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_localized_blocks
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.localized_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:03:03.960181+00:00
-- url     : https://prove2.me/theorems/175e54d0-34cb-497c-912a-40fcc61ab67b
-- title:
--   BDL26 RXPhysical Star Transport: localized blocks
-- statement:
--   The only supplied support premise concerns the original error difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L176-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L176-L182

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.localized_blocks (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    BDL26RXFiniteBlockTransport.Localized S depth i h {parentX S depth i h u}
      (incidentQ S depth i (parentX S depth i h u)) a b := by sorry
