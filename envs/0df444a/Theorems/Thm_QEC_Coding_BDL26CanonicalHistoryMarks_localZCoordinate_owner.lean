-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZCoordinate_owner
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.localZCoordinate_owner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:07:54.205345+00:00
-- url     : https://prove2.me/theorems/fcd0e374-8627-4a8c-9ccd-3d28385782fe
-- title:
--   BDL26 Canonical History Marks: local ZCoordinate owner
-- statement:
--   The BDL26 Canonical History Marks construction uses the local ZCoordinate owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L32-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L32-L34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.localZCoordinate_owner (S : OddScale) (n : Nat) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    baseSyndromeOwner S n (localZCoordinate S n x f) = localZ S x f := by sorry
