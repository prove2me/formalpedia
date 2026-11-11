-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_succ
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:11:31.193181+00:00
-- url     : https://prove2.me/theorems/8364019d-f519-44be-9112-56ed78520d09
-- title:
--   BDL26 History Error Telescoping: assembled Prefix succ
-- statement:
--   The BDL26 History Error Telescoping construction uses the assembled Prefix succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L419-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L419-L436

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.assembledPrefix_succ (sigma : TopInput S n) (i : StepIndex n) :
    assembledPrefix S n sigma i.succ = (actualOutput S n sigma i).correction +
      ((SuffixData S n).selectedMap i).map1 (assembledPrefix S n sigma i.castSucc) := by sorry
