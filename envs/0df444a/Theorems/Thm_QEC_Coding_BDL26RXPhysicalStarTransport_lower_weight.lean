-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_weight
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.lower_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:04:06.99465+00:00
-- url     : https://prove2.me/theorems/f28fc438-1e5f-4cf9-913b-1b6094887eb5
-- title:
--   BDL26 RXPhysical Star Transport: lower weight
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the lower weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L252-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L252-L258

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.lower_weight (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    HammingWeight (L S depth i h u a b) ≤
        (physicalXStar (state S i.val).presentation (parentX S depth i h u)).card ∧
      (physicalXStar (state S i.val).presentation (parentX S depth i h u)).card ≤ 7 := by sorry
