-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_vertical_incident
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.vertical_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:40:00.031517+00:00
-- url     : https://prove2.me/theorems/e5b71efe-0a1a-430b-8157-d239e0e0fec9
-- title:
--   BDL26 RZPhysical Star Transport: vertical incident
-- statement:
--   The BDL26 RZPhysical Star Transport construction uses the vertical incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L412-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L412-L421

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalStarTransport.vertical_incident (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    (state S (i.val+1)).presentation.qz (verticalPhysical S depth i odd z v)
      (verticalCentre S depth i odd z v)=true := by sorry
