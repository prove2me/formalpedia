-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_base_parent_edge
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.base_parent_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:03:14.653212+00:00
-- url     : https://prove2.me/theorems/872b6ab9-8da9-44e4-8123-e5d173e5d015
-- title:
--   BDL26 Canonical History Marks: base parent edge
-- statement:
--   The actual inherited edge, without changing the graph or saturating parents.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L187-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L187-L193

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.base_parent_edge (v : GraphVertex S 2) (u : GraphVertex S 1)
    (hp : parent S 1 v = some u) :
    (decodingGraph S (n + 2)).adjacent (physicalNode S n 0 v) (oneNode S n u) := by sorry
