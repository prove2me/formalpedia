-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_mem_physicalNodes
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.mem_physicalNodes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:03:04.556281+00:00
-- url     : https://prove2.me/theorems/a012e36d-42dd-48f4-8472-7ea8e8e1529d
-- title:
--   BDL26 Canonical History Marks: mem physical Nodes
-- statement:
--   The BDL26 Canonical History Marks construction uses the mem physical Nodes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L86-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean#L86-L100

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.mem_physicalNodes (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) :
    physicalNode S n i v ∈ physicalNodes S n sigma ↔ v ∈ physicalMarks S n sigma i := by sorry
