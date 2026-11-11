-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_oneMarks_in_rootComponent
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.oneMarks_in_rootComponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:04:48.449299+00:00
-- url     : https://prove2.me/theorems/54d96635-3d48-4139-8f36-4d7b5b220ca5
-- title:
--   BDL26 Canonical History Marks: one Marks in root Component
-- statement:
--   The BDL26 Canonical History Marks construction uses the one Marks in root Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L235-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L235-L240

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.oneMarks_in_rootComponent (u : GraphVertex S 1) (hu : u ∈ oneMarks S n sigma) :
    oneNode S n u ∈ rootComponent S n sigma := by sorry
