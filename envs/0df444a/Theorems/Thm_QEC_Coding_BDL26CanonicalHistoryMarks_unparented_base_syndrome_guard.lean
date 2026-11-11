-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_unparented_base_syndrome_guard
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.unparented_base_syndrome_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:55:47.951509+00:00
-- url     : https://prove2.me/theorems/95654e4f-6696-49e2-be1a-b9caaba8f9de
-- title:
--   BDL26 Canonical History Marks: unparented base syndrome guard
-- statement:
--   A positive-dimensional local-Z graph node need not have a parent. Its
--   literal syndrome guard still marks it, without adding a connector edge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L107-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L107-L112

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.unparented_base_syndrome_guard
    (v : GraphVertex S 2) (hv : parent S 1 v = none)
    (p : FamilyZ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (ho : baseSyndromeOwner S n p = v) (hp : (baseInput S n sigma).val p ≠ 0) :
    v ∈ baseMarks S n sigma ∧ parent S 1 v = none := by sorry
