-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualOutput_correction
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actualOutput_correction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:11:11.021166+00:00
-- url     : https://prove2.me/theorems/acf498ff-f0bb-4d3c-bc7c-34f003a3e2d4
-- title:
--   BDL26 History Error Telescoping: actual Output correction
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual Output correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L335-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L335-L338

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actualOutput_correction (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).correction =
      (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
        (actualInputs S n sigma i.succ)).correction := by sorry
