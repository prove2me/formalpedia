-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_historyReadout_cons
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:02:45.26596+00:00
-- url     : https://prove2.me/theorems/b79cf429-4c99-4b48-b5bb-e46c26eb80b9
-- title:
--   BDL26 History Syndrome Sensitivity: history Readout cons
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the history Readout cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L116-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L116-L121

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_cons (D : BDL26DecoderData depth C0 C1 C2)
    (e : CorrectionHistoryEntry D) (H : CorrectionHistory D) (a : LevelIndex depth) :
    historyInputReadout D (e :: H) a =
      (if h : e.inputSyndrome.1 = a then h ▸ e.inputSyndrome.2.val else 0) +
        historyInputReadout D H a := by sorry
