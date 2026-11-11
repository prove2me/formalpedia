-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_historyReadout_step_same
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_step_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:49:53.141616+00:00
-- url     : https://prove2.me/theorems/a72b0313-9a9b-4fc7-9145-865876faadf5
-- title:
--   BDL26 History Syndrome Sensitivity: history Readout step same
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the history Readout step same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L123-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L123-L129

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_step_same (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (out : AssemblyStepOutput D i) (H : CorrectionHistory D) :
    historyInputReadout D (.step i out :: H) i.succ =
      out.input.val + historyInputReadout D H i.succ := by sorry
