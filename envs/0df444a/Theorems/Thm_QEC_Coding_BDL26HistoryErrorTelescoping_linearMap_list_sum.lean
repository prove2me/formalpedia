-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearMap_list_sum
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.linearMap_list_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:12:37.627667+00:00
-- url     : https://prove2.me/theorems/68ef3851-851d-4edc-a37a-b841f5b27f61
-- title:
--   BDL26 History Error Telescoping: linear Map list sum
-- statement:
--   The BDL26 History Error Telescoping construction uses the linear Map list sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L482-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L482-L487

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.linearMap_list_sum {W : Type u} {Z : Type v}
    [AddCommMonoid W] [Module BDL26Field W] [AddCommMonoid Z] [Module BDL26Field Z]
    (f : W →ₗ[BDL26Field] Z) (L : List W) : (L.map f).sum = f L.sum := by sorry
