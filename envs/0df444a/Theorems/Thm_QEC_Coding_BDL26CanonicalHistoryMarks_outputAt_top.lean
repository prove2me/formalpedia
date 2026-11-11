-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_outputAt_top
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.outputAt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:02:08.684171+00:00
-- url     : https://prove2.me/theorems/85cef84f-70b2-48d2-888a-46ad0603c8b5
-- title:
--   BDL26 Canonical History Marks: output At top
-- statement:
--   The literal top snapshot is the real top adapter output for any non-base depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L152-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L152-L168

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.outputAt_top (m : Nat) (s : Input S (m + 1)) :
    outputAt S (m + 1) s (Fin.last m) =
      actualStep S ((m + 1) + 2) (LevelTwoHistory.physicalStep (Fin.last m)) s := by sorry
