-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualCorrection_split
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actualCorrection_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:30:50.1372+00:00
-- url     : https://prove2.me/theorems/2dddfb35-d022-4cdf-a56b-29fc88dece1e
-- title:
--   BDL26 History Error Telescoping: actual Correction split
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual Correction split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L541-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L541-L547

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actualCorrection_split (sigma : TopInput S n) :
    historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) =
      correctionIntervalSum S n sigma 0 (TopIndex n) +
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          ((actualBase S n).decode (actualInputs S n sigma 0)) := by sorry
