-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_split
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:38:30.481672+00:00
-- url     : https://prove2.me/theorems/6bbb2ba0-1059-4a09-b2c8-57370218924d
-- title:
--   BDL26 History Error Telescoping: assembled Prefix split
-- statement:
--   The BDL26 History Error Telescoping construction uses the assembled Prefix split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L352-L356
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L352-L356

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_split (sigma : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val) :
    assembledPrefix S n sigma b = correctionIntervalSum S n sigma a b +
      intervalMap1 (SuffixData S n) a b hab (assembledPrefix S n sigma a) := by sorry
