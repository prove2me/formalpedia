-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_succ
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:25:29.930565+00:00
-- url     : https://prove2.me/theorems/5c361413-aee5-4144-9216-78f916450b21
-- title:
--   BDL26 History Logical Residual: interval Cocycle succ
-- statement:
--   The BDL26 History Logical Residual construction uses the interval Cocycle succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L55-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L55-L59

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_succ (a : LevelIndex n) (i : StepIndex n) (hai : a.val ≤ i.val) :
    intervalCocycle S n a i.succ (by change a.val ≤ i.val+1; omega) =
      (cocycleEdge S n i).comp (intervalCocycle S n a i.castSucc hai) := by sorry
