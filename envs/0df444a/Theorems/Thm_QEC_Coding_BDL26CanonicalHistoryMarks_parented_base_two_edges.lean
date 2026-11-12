-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_parented_base_two_edges
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.parented_base_two_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:04:15.522541+00:00
-- url     : https://prove2.me/theorems/accdcbd2-5db7-47f2-8180-6a3bb478ccd8
-- title:
--   BDL26 Canonical History Marks: parented base two edges
-- statement:
--   The source bottom closure gives two genuine inherited marked edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L203-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L203-L212

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.parented_base_two_edges (v : GraphVertex S 2) (hv : v ∈ baseMarks S n sigma)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    markedAdjacent S n sigma (physicalNode S n 0 v) (oneNode S n u) ∧
    markedAdjacent S n sigma (oneNode S n u) (root S n) := by sorry
