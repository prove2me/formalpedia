-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_word
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:04:07.088906+00:00
-- url     : https://prove2.me/theorems/c1d65004-8ebc-40fe-ac66-c35833923a4c
-- title:
--   BDL26 History Logical Residual: interval Cocycle word
-- statement:
--   The BDL26 History Logical Residual construction uses the interval Cocycle word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L140-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L140-L143

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_word (a b : LevelIndex n) (hab : a.val ≤ b.val)
    (w : FC.Cocycle S (a.val+2)) :
    (intervalCocycle S n a b hab w).val = intervalMap1 (SuffixData S n) a b hab w.val := by sorry
