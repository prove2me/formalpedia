-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_step
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:26:40.363211+00:00
-- url     : https://prove2.me/theorems/8b704fed-1ae1-4cc6-b820-4a52ef9253f7
-- title:
--   BDL26 History Syndrome Sensitivity: actual Inputs step
-- statement:
--   Consecutive inputs are exactly the real selector's coarse output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L260-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Snapshots.lean#L260-L278

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_step (sigma : TopInput S n) (i : StepIndex n) :
    actualInputs S n sigma i.castSucc =
      (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
        (actualInputs S n sigma i.succ)).coarse := by sorry
