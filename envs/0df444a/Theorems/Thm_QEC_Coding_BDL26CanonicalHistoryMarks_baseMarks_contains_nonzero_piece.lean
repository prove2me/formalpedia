-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_baseMarks_contains_nonzero_piece
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.baseMarks_contains_nonzero_piece
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T20:44:11.37957+00:00
-- url     : https://prove2.me/theorems/425f462a-4455-4485-bd65-d5f8a1467288
-- title:
--   BDL26 Canonical History Marks: base Marks contains nonzero piece
-- statement:
--   A nonzero closed fibre is retained by guard 1.2 without testing its boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L101-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L101-L103

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.baseMarks_contains_nonzero_piece (v : GraphVertex S 2)
    (h : basePiece S n sigma v ≠ 0) : v ∈ baseMarks S n sigma := by sorry
