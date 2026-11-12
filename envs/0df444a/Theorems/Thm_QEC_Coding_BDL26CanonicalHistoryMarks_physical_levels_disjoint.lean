-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physical_levels_disjoint
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.physical_levels_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:11:26.065013+00:00
-- url     : https://prove2.me/theorems/85eb3dea-fdb3-4e4a-b29a-74c3c2c5f468
-- title:
--   BDL26 Canonical History Marks: physical levels disjoint
-- statement:
--   The BDL26 Canonical History Marks construction uses the physical levels disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L77-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L77-L84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.physical_levels_disjoint (i k : LevelIndex n) (h : i ≠ k)
    (u : GraphVertex S (i.val + 2)) (v : GraphVertex S (k.val + 2)) :
    physicalNode S n i u ≠ physicalNode S n k v := by sorry
