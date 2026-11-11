-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_step
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:43:45.251527+00:00
-- url     : https://prove2.me/theorems/a0eb6916-8e04-457c-9780-b5b8f3affe3d
-- title:
--   BDL26 Canonical History Marks: entry At step
-- statement:
--   The BDL26 Canonical History Marks construction uses the entry At step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L78-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L78-L102

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_step (i : StepIndex n) :
    entryAt S n sigma i.succ = .step i
      (LevelTwoHistory.suffixOutput (indexedDecoderData S (n + 2)) i
        (outputAt S n sigma i)) := by sorry
