-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.suffix_delta0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:03:46.730878+00:00
-- url     : https://prove2.me/theorems/e2146884-56cf-46da-b589-b8c2098030d6
-- title:
--   BDL26 History Logical Residual: suffix delta0
-- statement:
--   These are equalities of the actual differentials, not new complexes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L24-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L24-L28

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.suffix_delta0 (i : LevelIndex n) :
    (SuffixData S n).family.coboundary0 i =
      tannerCoboundary0 (state S (i.val+2)).presentation := by sorry
