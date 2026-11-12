-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_actual_parented_base_in_rootComponent
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.actual_parented_base_in_rootComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:18:03.303755+00:00
-- url     : https://prove2.me/theorems/9d787490-4ff8-41ef-b991-7aee6c2dc364
-- title:
--   BDL26 Canonical History Marks: actual parented base in root Component
-- statement:
--   The BDL26 Canonical History Marks construction uses the actual parented base in root Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L269-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L269-L274

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.actual_parented_base_in_rootComponent (j : Nat) (s : Input S (2 * j))
    (v : GraphVertex S 2) (hv : physicalNode S (2 * j) 0 v ∈ actualMarks S j s)
    (u : GraphVertex S 1) (hp : parent S 1 v = some u) :
    physicalNode S (2 * j) 0 v ∈ actualRootComponent S j s := by sorry
