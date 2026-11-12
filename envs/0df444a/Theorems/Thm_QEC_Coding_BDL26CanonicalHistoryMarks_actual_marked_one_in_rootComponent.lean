-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_actual_marked_one_in_rootComponent
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.actual_marked_one_in_rootComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:14:56.923699+00:00
-- url     : https://prove2.me/theorems/d5afb70c-5e20-45ef-bba8-52e1fe307d1f
-- title:
--   BDL26 Canonical History Marks: actual marked one in root Component
-- statement:
--   An endpoint takes the original actual vertex membership, without any
--   caller-supplied closure or root certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L264-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L264-L267

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.actual_marked_one_in_rootComponent (j : Nat) (s : Input S (2 * j))
    (u : GraphVertex S 1) (hu : oneNode S (2 * j) u ∈ actualMarks S j s) :
    oneNode S (2 * j) u ∈ actualRootComponent S j s := by sorry
