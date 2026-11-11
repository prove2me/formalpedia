-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_physicalMarks_step
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:15:28.347369+00:00
-- url     : https://prove2.me/theorems/ea1698bf-42cf-47d7-a228-3ef41ab900a6
-- title:
--   BDL26 Canonical History Marks: physical Marks step
-- statement:
--   The BDL26 Canonical History Marks construction uses the physical Marks step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L122-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/PhysicalMarks.lean#L122-L123

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step (i : StepIndex n) :
    physicalMarks S n sigma i.succ = aboveMarks S n sigma i := by sorry

attribute [defeq] QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step
