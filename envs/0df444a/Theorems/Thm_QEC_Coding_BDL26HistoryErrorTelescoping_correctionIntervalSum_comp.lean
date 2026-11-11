-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_correctionIntervalSum_comp
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:15:15.825542+00:00
-- url     : https://prove2.me/theorems/3b510c7c-13e0-480d-9130-5bbbd9e5413e
-- title:
--   BDL26 History Error Telescoping: correction Interval Sum comp
-- statement:
--   The BDL26 History Error Telescoping construction uses the correction Interval Sum comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L361-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L361-L366

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_comp (sigma : TopInput S n) (a b c : LevelIndex n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    correctionIntervalSum S n sigma a c =
      intervalMap1 (SuffixData S n) b c hbc (correctionIntervalSum S n sigma a b) +
        correctionIntervalSum S n sigma b c := by sorry
