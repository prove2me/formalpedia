-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_map1_with_potential
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.map1_with_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:56:50.860208+00:00
-- url     : https://prove2.me/theorems/f784655f-71bf-4a26-a400-5630a67e451c
-- title:
--   BDL26 RXPhysical Star Transport: map1 with potential
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the map1 with potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L200-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L200-L205

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_with_potential

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.map1_with_potential (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h u a b) := by sorry
