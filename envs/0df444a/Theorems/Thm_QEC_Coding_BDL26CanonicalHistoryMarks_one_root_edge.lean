-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_one_root_edge
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.one_root_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:27:25.801531+00:00
-- url     : https://prove2.me/theorems/a283a12f-bc2c-4282-af52-18cdb15d49ab
-- title:
--   BDL26 Canonical History Marks: one root edge
-- statement:
--   The BDL26 Canonical History Marks construction uses the one root edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L195-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L195-L200

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.one_root_edge (u : GraphVertex S 1) :
    (decodingGraph S (n + 2)).adjacent (oneNode S n u) (root S n) := by sorry
