-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_inputAt_step
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.inputAt_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:01:33.340403+00:00
-- url     : https://prove2.me/theorems/1da794d2-50d9-4667-99e7-db187869c13b
-- title:
--   BDL26 Canonical History Marks: input At step
-- statement:
--   The BDL26 Canonical History Marks construction uses the input At step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L57-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L57-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.inputAt_step (i : StepIndex n) (O : AssemblyStepOutput (Data S n) i)
    (he : CorrectionHistoryEntry.step i O ∈ actualHistory S n sigma) :
    inputAt S n sigma i.succ = O.input := by sorry
