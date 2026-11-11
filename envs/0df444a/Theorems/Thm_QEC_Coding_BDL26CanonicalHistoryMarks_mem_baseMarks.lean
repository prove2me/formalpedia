-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_baseMarks
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_baseMarks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:25:23.18819+00:00
-- url     : https://prove2.me/theorems/90178734-bd64-4325-9b1b-27efcfb5fed8
-- title:
--   BDL26 Canonical History Marks: mem base Marks
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem base Marks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L94-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L94-L98

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_baseMarks (v : GraphVertex S 2) : v ∈ baseMarks S n sigma ↔
    (∃ p, baseSyndromeOwner S n p = v ∧ (baseInput S n sigma).val p ≠ 0) ∨
    basePiece S n sigma v ≠ 0 ∨
    (∃ u p, baseSyndromeOwner S n p = v ∧ basePieceBoundary S n sigma u p ≠ 0) := by sorry
