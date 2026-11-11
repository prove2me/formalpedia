-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_oneMarks
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_oneMarks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:25:28.116197+00:00
-- url     : https://prove2.me/theorems/08e8f786-bb3d-4526-b9c6-33ae48dae47e
-- title:
--   BDL26 Canonical History Marks: mem one Marks
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem one Marks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L38-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L38-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_oneMarks (u : GraphVertex S 1) : u ∈ oneMarks S n sigma ↔
    ∃ v ∈ baseMarks S n sigma, parent S 1 v = some u := by sorry
