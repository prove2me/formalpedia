-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_perturbationCenter_incident
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.perturbationCenter_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:34:36.715468+00:00
-- url     : https://prove2.me/theorems/150eab3f-4643-414b-a328-004f4a842365
-- title:
--   BDL26 RXPhysical Star Transport: perturbation Center incident
-- statement:
--   The BDL26 RXPhysical Star Transport construction uses the perturbation Center incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L351-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L351-L354

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

theorem QEC.Coding.BDL26RXPhysicalStarTransport.perturbationCenter_incident (p : FamilyQ S depth i.succ) :
    p ∈ upperStar S depth i (perturbationCenter S depth i p) := by sorry
