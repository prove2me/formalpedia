-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_incident_card_le_seven
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.incident_card_le_seven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:20:57.077949+00:00
-- url     : https://prove2.me/theorems/6a7259c2-db5b-4bce-99aa-50c644d8f371
-- title:
--   BDL26 RXPhysical Star Transport: incident card le seven
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the incident card le seven property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L245-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L245-L250

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.incident_card_le_seven (x : XCoord S i) :
    (physicalXStar (state S i.val).presentation x).card ≤ 7 := by sorry
