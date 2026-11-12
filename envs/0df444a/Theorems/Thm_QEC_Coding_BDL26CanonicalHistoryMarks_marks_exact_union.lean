-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_marks_exact_union
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.marks_exact_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:11:18.417361+00:00
-- url     : https://prove2.me/theorems/b28e37ab-2536-4daa-a736-dd53ffbfff06
-- title:
--   BDL26 Canonical History Marks: marks exact union
-- statement:
--   The BDL26 Canonical History Marks construction uses the marks exact union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L55-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L55-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.marks_exact_union : marks S n sigma =
    (Finset.univ.biUnion (fun i : LevelIndex n =>
      (physicalMarks S n sigma i).image (physicalNode S n i))) ∪
    (oneMarks S n sigma).image (oneNode S n) ∪
    (rootMarks S n sigma).image (fun _ => root S n) := by sorry
