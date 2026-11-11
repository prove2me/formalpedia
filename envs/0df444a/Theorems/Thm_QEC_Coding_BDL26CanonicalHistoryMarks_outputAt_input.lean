-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_outputAt_input
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.outputAt_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:48:07.787329+00:00
-- url     : https://prove2.me/theorems/4078226b-7722-4dec-bc41-a5e9eb240c2e
-- title:
--   BDL26 Canonical History Marks: output At input
-- statement:
--   The BDL26 Canonical History Marks construction uses the output At input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L128-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L128-L130

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.outputAt_input (i : StepIndex n) :
    (outputAt S n sigma i).input = inputAt S n sigma i.succ := by sorry
