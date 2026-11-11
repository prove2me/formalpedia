-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_correctionIntervalSum_succ
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:40:36.177814+00:00
-- url     : https://prove2.me/theorems/f28ee46f-1db4-446b-b615-56dafb09b70c
-- title:
--   BDL26 History Error Telescoping: correction Interval Sum succ
-- statement:
--   The BDL26 History Error Telescoping construction uses the correction Interval Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L444-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L444-L450

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_succ (sigma : TopInput S n)
    (a : LevelIndex n) (i : StepIndex n) (hai : a.val ≤ i.val) :
    correctionIntervalSum S n sigma a i.succ =
      ((SuffixData S n).selectedMap i).map1 (correctionIntervalSum S n sigma a i.castSucc) +
        (actualOutput S n sigma i).correction := by sorry
