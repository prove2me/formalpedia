-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_aboveMarks
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_aboveMarks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T20:39:14.507114+00:00
-- url     : https://prove2.me/theorems/b0e61f6f-9b52-4641-b005-f45b6498d509
-- title:
--   BDL26 Canonical History Marks: mem above Marks
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem above Marks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L45-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L45-L51

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_aboveMarks (i : StepIndex n) (v : GraphVertex S (i.val + 3)) :
    v ∈ aboveMarks S n sigma i ↔
      (∃ p, syndromeOwner S n i p = v ∧ (outputAt S n sigma i).input.val p ≠ 0) ∨
      (∃ a, pieceOwner S n sigma i a = v ∧ (outputAt S n sigma i).componentAt a ≠ 0) ∨
      (∃ a p, syndromeOwner S n i p = v ∧
        (outputAt S n sigma i).componentCoboundaryAt a p ≠ 0) := by sorry
