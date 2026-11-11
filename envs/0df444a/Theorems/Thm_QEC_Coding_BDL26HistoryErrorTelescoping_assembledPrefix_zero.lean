-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_zero
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:40:27.482882+00:00
-- url     : https://prove2.me/theorems/ff3ba4d2-e9f4-40ee-9165-28108689abbd
-- title:
--   BDL26 History Error Telescoping: assembled Prefix zero
-- statement:
--   The BDL26 History Error Telescoping construction uses the assembled Prefix zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L393-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L393-L405

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_zero (sigma : TopInput S n) :
    assembledPrefix S n sigma 0 = (actualBase S n).decode (actualInputs S n sigma 0) := by sorry
