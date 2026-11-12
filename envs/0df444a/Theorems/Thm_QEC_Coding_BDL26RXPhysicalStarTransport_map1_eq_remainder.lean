-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_map1_eq_remainder
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.map1_eq_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:51:54.375823+00:00
-- url     : https://prove2.me/theorems/fe4b992e-2e3c-4a40-8ff3-3e7499b53f71
-- title:
--   BDL26 RXPhysical Star Transport: map1 eq remainder
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the map1 eq remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L194-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L194-L198

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.map1_eq_remainder (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=R S depth i h u a b := by sorry
