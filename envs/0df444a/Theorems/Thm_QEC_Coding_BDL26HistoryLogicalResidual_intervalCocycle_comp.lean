-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_comp
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:01:06.040327+00:00
-- url     : https://prove2.me/theorems/cadd4fc0-d764-4597-8a04-b91d241875bf
-- title:
--   BDL26 History Logical Residual: interval Cocycle comp
-- statement:
--   The BDL26 History Logical Residual construction uses the interval Cocycle comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L61-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L61-L66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.intervalCocycle_comp (a b c : LevelIndex n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalCocycle S n a c (hab.trans hbc) =
      (intervalCocycle S n b c hbc).comp (intervalCocycle S n a b hab) := by sorry
