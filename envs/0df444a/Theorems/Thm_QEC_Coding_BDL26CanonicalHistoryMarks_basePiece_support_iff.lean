-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_basePiece_support_iff
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.basePiece_support_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:41:43.910777+00:00
-- url     : https://prove2.me/theorems/fd1e4093-7570-4a11-bb68-68b342e0ba28
-- title:
--   BDL26 Canonical History Marks: base Piece support iff
-- statement:
--   The BDL26 Canonical History Marks construction uses the base Piece support iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L69-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L69-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.basePiece_support_iff (v : GraphVertex S 2)
    (p : FamilyQ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) :
    p ∈ hammingSupport (basePiece S n sigma v) ↔
      baseCorrectionOwner S n p = v ∧ baseCorrection S n sigma p ≠ 0 := by sorry
