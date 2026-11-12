-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_top_marks_are_Z
-- name    : QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_marks_are_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:14:05.399126+00:00
-- url     : https://prove2.me/theorems/2bc1e141-9b69-4839-9627-68d93cc42eb7
-- title:
--   BDL26 Canonical Root Witness Counterexample: actual top marks are Z
-- statement:
--   The true mark definitions add only Z-type vertices at physical top C4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L935-L955
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalRootWitnessCounterexample.lean#L935-L955

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open BDL26RXLocalReplacement BDL26RXStagedRestriction

theorem QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_marks_are_Z (S : OddScale)
    (sigma : BDL26CanonicalHistoryMarks.Input S 2) :
    ∀ v : GraphVertex S 4,
      actualTopNode S v ∈
        BDL26CanonicalHistoryMarks.marks S 2 sigma → ∃ z, v = zVertex S 3 z := by sorry
