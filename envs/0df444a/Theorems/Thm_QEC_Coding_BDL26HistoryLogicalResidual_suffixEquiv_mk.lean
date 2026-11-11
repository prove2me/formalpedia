-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_mk
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:04:59.84448+00:00
-- url     : https://prove2.me/theorems/b6c3ceed-7d8d-46e1-8cfe-01c4f289cb35
-- title:
--   BDL26 History Logical Residual: suffix Equiv mk
-- statement:
--   The BDL26 History Logical Residual construction uses the suffix Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L145-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L145-L149

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_mk (a b : LevelIndex n) (hab : a.val ≤ b.val)
    (w : FC.Cocycle S (a.val+2)) :
    suffixEquiv S n a b (FC.classOf S (a.val+2) w) =
      FC.classOf S (b.val+2) (intervalCocycle S n a b hab w) := by sorry
