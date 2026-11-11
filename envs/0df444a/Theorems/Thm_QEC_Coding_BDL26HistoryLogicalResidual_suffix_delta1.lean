-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.suffix_delta1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:03:53.620094+00:00
-- url     : https://prove2.me/theorems/1d856205-210a-40cc-83b8-70cce32f2302
-- title:
--   BDL26 History Logical Residual: suffix delta1
-- statement:
--   The BDL26 History Logical Residual construction uses the suffix delta1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L30-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L30-L34

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.suffix_delta1 (i : LevelIndex n) :
    (SuffixData S n).family.coboundary1 i =
      tannerCoboundary1 (state S (i.val+2)).presentation := by sorry
