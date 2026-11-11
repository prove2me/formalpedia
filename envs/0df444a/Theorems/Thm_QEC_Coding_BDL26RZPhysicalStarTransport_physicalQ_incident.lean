-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_physicalQ_incident
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:38:39.858348+00:00
-- url     : https://prove2.me/theorems/85cda034-d316-49d5-b0ff-6c99c730fee1
-- title:
--   BDL26 RZPhysical Star Transport: physical Q incident
-- statement:
--   The BDL26 RZPhysical Star Transport construction uses the physical Q incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L347-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L347-L357

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.physicalQ_incident (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    (state S (i.val+1)).presentation.qz (physicalQ S depth i odd q v)
      (qCentre S depth i odd q z hqz v)=true := by sorry
