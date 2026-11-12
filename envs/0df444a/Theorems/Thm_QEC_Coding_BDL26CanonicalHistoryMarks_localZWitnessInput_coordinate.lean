-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZWitnessInput_coordinate
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.localZWitnessInput_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:07:51.070943+00:00
-- url     : https://prove2.me/theorems/2a42b37f-187a-4a43-8f8b-6dbdcdc0dbe0
-- title:
--   BDL26 Canonical History Marks: local ZWitness Input coordinate
-- statement:
--   The BDL26 Canonical History Marks construction uses the local ZWitness Input coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L65-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L65-L78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.localZWitnessInput_coordinate (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    (localZWitnessInput S).val (localZCoordinate S 0 x f) =
      BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 (.inl (.inl ⟨x, f⟩)) := by sorry
