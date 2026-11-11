-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalNode_level
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.physicalNode_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:52:16.281233+00:00
-- url     : https://prove2.me/theorems/4c6146be-7117-4a6e-a09b-0c4f2bbb5eda
-- title:
--   BDL26 Canonical History Marks: physical Node level
-- statement:
--   The BDL26 Canonical History Marks construction uses the physical Node level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L74-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L74-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.physicalNode_level (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    (physicalNode S n i v).1.val = i.val + 2 := by sorry
