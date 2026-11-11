-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalNodes_min_level
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.physicalNodes_min_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:26:08.747895+00:00
-- url     : https://prove2.me/theorems/60524308-28f1-4002-9b1f-de0517b37782
-- title:
--   BDL26 Canonical History Marks: physical Nodes min level
-- statement:
--   The BDL26 Canonical History Marks construction uses the physical Nodes min level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L102-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L102-L107

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.physicalNodes_min_level (w : Node S n) (hw : w ∈ physicalNodes S n sigma) :
    2 ≤ w.1.val := by sorry
