-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_self
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:11:56.004488+00:00
-- url     : https://prove2.me/theorems/a74b9720-bd5b-4915-9238-4d88fe28b5ad
-- title:
--   BDL26 History Logical Residual: suffix Equiv self
-- statement:
--   The BDL26 History Logical Residual construction uses the suffix Equiv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L73-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L73-L74

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_self (a : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n a a x = x := by sorry
