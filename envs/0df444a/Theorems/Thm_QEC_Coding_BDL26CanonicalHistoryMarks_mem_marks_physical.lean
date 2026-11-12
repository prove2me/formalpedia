-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_marks_physical
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_marks_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:36:05.233508+00:00
-- url     : https://prove2.me/theorems/1602176a-e80e-46a6-8830-111f10d36c58
-- title:
--   BDL26 Canonical History Marks: mem marks physical
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem marks physical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L109-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L109-L124

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_marks_physical (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    physicalNode S n i v ∈ marks S n sigma ↔ v ∈ physicalMarks S n sigma i := by sorry
