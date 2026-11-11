-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZ_unparented
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.localZ_unparented
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:09:03.959353+00:00
-- url     : https://prove2.me/theorems/67dd6d2a-b713-42cf-9d00-80e0b979560d
-- title:
--   BDL26 Canonical History Marks: local Z unparented
-- statement:
--   The BDL26 Canonical History Marks construction uses the local Z unparented property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L21-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L21-L23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.localZ_unparented (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    parent S 1 (localZ S x f) = none := by sorry
