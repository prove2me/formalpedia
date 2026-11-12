-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_coarse_apply
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.coarse_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:58:06.946661+00:00
-- url     : https://prove2.me/theorems/5ab5dbd8-e9c9-4853-85f1-c07ed1a312a6
-- title:
--   BDL26 RXPhysical Star Transport: coarse apply
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the coarse apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L260-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L260-L266

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_apply
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_apply

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.coarse_apply (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) (z : ZCoord S i) :
    (coarseSum S depth i h a b).val z =
      ∑ q ∈ physicalXStar (state S i.val).presentation (parentX S depth i h u),
        L S depth i h u a b q * (if (state S i.val).presentation.qz q z=true then 1 else 0) := by sorry
