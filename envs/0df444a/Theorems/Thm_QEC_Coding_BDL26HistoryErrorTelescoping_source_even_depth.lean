-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_source_even_depth
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.source_even_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:49:37.759401+00:00
-- url     : https://prove2.me/theorems/50971abc-60eb-416d-95a6-cfeeec17b68e
-- title:
--   BDL26 History Error Telescoping: source even depth
-- statement:
--   Source-even depth includes k=1, whose suffix has no nonbase step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L449-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L449-L449

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.source_even_depth (k : Nat) (hk : 1 ≤ k) : 2*(k-1)+2=2*k := by sorry
