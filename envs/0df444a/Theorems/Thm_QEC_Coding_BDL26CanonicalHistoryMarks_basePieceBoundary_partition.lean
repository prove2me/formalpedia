-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_basePieceBoundary_partition
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.basePieceBoundary_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:42:12.469474+00:00
-- url     : https://prove2.me/theorems/39349b9c-2dc0-4b4e-a92b-0446fcee0721
-- title:
--   BDL26 Canonical History Marks: base Piece Boundary partition
-- statement:
--   The BDL26 Canonical History Marks construction uses the base Piece Boundary partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L81-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L81-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.basePieceBoundary_partition :
    (∑ v : GraphVertex S 2, basePieceBoundary S n sigma v) =
      (baseInput S n sigma).val := by sorry
