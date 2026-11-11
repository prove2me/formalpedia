-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZWitnessLower_val
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.localZWitnessLower_val
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:11:15.101317+00:00
-- url     : https://prove2.me/theorems/99090a83-15b3-4076-941d-2e6dd807ef5c
-- title:
--   BDL26 Canonical History Marks: local ZWitness Lower val
-- statement:
--   The BDL26 Canonical History Marks construction uses the local ZWitness Lower val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L55-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L55-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.localZWitnessLower_val (S : OddScale) : (localZWitnessLower S).val =
    BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 := by sorry
