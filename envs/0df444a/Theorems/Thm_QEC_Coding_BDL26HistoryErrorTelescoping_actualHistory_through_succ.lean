-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualHistory_through_succ
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actualHistory_through_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:14:22.476816+00:00
-- url     : https://prove2.me/theorems/27098226-c953-4bc2-ba21-3092f5adfb83
-- title:
--   BDL26 History Error Telescoping: actual History through succ
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual History through succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L407-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L407-L417

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actualHistory_through_succ (sigma : TopInput S n) (i : StepIndex n) :
    historyThrough (SuffixData S n) (actualHistory S n sigma) i.succ =
      .step i (actualOutput S n sigma i) ::
        historyThrough (SuffixData S n) (actualHistory S n sigma) i.castSucc := by sorry
