-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_lifted_actual_components
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.lifted_actual_components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:45:09.278663+00:00
-- url     : https://prove2.me/theorems/00f09a4d-f88f-43e0-a9c2-8ca7f1101829
-- title:
--   BDL26 History Error Telescoping: lifted actual components
-- statement:
--   The BDL26 History Error Telescoping construction uses the lifted actual components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L533-L539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L533-L539

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.lifted_actual_components (sigma : TopInput S n) (i : StepIndex n)
    (b : LevelIndex n) (hib : i.succ.val ≤ b.val) :
    intervalMap1 (SuffixData S n) i.succ b hib (actualOutput S n sigma i).correction =
      ((actualOutput S n sigma i).localComponents.map
        (intervalMap1 (SuffixData S n) i.succ b hib)).sum := by sorry
