-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_sum_filterMap_eq_sum_getD
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.sum_filterMap_eq_sum_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:34:12.333199+00:00
-- url     : https://prove2.me/theorems/756ea408-69ed-44d0-be10-d70311943897
-- title:
--   BDL26 History Error Telescoping: sum filter Map eq sum get D
-- statement:
--   The BDL26 History Error Telescoping construction uses the sum filter Map eq sum get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L21-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L21-L28

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
variable {A : Type u} {W : Type v} [AddCommMonoid W]

theorem QEC.Coding.BDL26HistoryErrorTelescoping.sum_filterMap_eq_sum_getD (f : A → Option W) (L : List A) :
    (L.filterMap f).sum = (L.map (fun a => (f a).getD 0)).sum := by sorry
