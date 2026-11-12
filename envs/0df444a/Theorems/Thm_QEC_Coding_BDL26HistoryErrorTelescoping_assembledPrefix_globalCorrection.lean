-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_globalCorrection
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_globalCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:43:44.578611+00:00
-- url     : https://prove2.me/theorems/5ed95902-e060-4541-bf4b-98344b58ee92
-- title:
--   BDL26 History Error Telescoping: assembled Prefix global Correction
-- statement:
--   The BDL26 History Error Telescoping construction uses the assembled Prefix global Correction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L373-L378
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L373-L378

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_globalCorrection (sigma : TopInput S n) :
    assembledPrefix S n sigma (TopIndex n) =
      globalCorrection (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma := by sorry
