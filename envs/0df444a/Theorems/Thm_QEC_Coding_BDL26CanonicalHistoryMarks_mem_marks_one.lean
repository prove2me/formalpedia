-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_one
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_marks_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:53:30.636426+00:00
-- url     : https://prove2.me/theorems/dc797c5a-a85b-4852-9220-b33db8b9c7af
-- title:
--   BDL26 Canonical History Marks: mem marks one
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem marks one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L126-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L126-L142

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_marks_one (u : GraphVertex S 1) :
    oneNode S n u ∈ marks S n sigma ↔ u ∈ oneMarks S n sigma := by sorry
