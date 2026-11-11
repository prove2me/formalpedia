-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_readout
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_readout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:24:25.064205+00:00
-- url     : https://prove2.me/theorems/b6919d53-8221-4c84-ad9f-918edda176bd
-- title:
--   BDL26 History Syndrome Sensitivity: actual Inputs readout
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the actual Inputs readout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L243-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L243-L253

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
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_readout (sigma : TopInput S n) (a : LevelIndex n) :
    actualReadout S n sigma a = (actualInputs S n sigma a).val := by sorry
