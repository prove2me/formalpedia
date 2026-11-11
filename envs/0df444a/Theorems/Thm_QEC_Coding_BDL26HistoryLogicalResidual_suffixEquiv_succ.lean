-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffixEquiv_succ
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:10:41.082327+00:00
-- url     : https://prove2.me/theorems/ef779b4b-58ab-451e-a5e3-c97a1e7376d0
-- title:
--   BDL26 History Logical Residual: suffix Equiv succ
-- statement:
--   The BDL26 History Logical Residual construction uses the suffix Equiv succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L84-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L84-L90

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.suffixEquiv_succ (a : LevelIndex n) (i : StepIndex n)
    (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n a i.succ x =
      FC.stepEquiv S (i.val+2) (suffixEquiv S n a i.castSucc x) := by sorry
