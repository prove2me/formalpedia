-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_base
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_base
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:50:59.917011+00:00
-- url     : https://prove2.me/theorems/fe1574e7-3255-4014-b5e1-25def5ecf680
-- title:
--   BDL26 Canonical History Marks: entry At base
-- statement:
--   The base entry is unique and its correction is the real selected decoder.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L108-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L108-L126

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_base :
    ∃ B : RecursiveBaseLevelCorrection (Data S n),
      entryAt S n sigma 0 = .base B ∧
      B.input = baseInput S n sigma ∧ B.correction = baseCorrection S n sigma := by sorry
