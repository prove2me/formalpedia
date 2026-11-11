-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_eq
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:43:03.921223+00:00
-- url     : https://prove2.me/theorems/c320aa37-b5ce-451f-bd65-fa9b4599621a
-- title:
--   BDL26 Canonical History Marks: entry At eq
-- statement:
--   The BDL26 Canonical History Marks construction uses the entry At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L49-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L49-L52

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_eq (i : LevelIndex n) (e : CorrectionHistoryEntry (Data S n))
    (he : e ∈ actualHistory S n sigma) (hi : e.inputSyndrome.1 = i) :
    entryAt S n sigma i = e := by sorry
