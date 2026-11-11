-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_historyReadout_step_ne
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_step_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:49:51.655317+00:00
-- url     : https://prove2.me/theorems/28897d77-ed6e-442e-a2ee-2b40d3b3709a
-- title:
--   BDL26 History Syndrome Sensitivity: history Readout step ne
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the history Readout step ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L131-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L131-L139

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_step_ne (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (out : AssemblyStepOutput D i) (H : CorrectionHistory D)
    (a : LevelIndex depth) (ha : i.succ ≠ a) :
    historyInputReadout D (.step i out :: H) a = historyInputReadout D H a := by sorry
