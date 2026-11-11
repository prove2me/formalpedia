-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualOutput_coarse
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actualOutput_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:15:00.427494+00:00
-- url     : https://prove2.me/theorems/dbd0ca63-b341-4cda-a6d4-af1e9840b5fb
-- title:
--   BDL26 History Error Telescoping: actual Output coarse
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual Output coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L340-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L340-L342

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actualOutput_coarse (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).coarse = actualInputs S n sigma i.castSucc := by sorry
