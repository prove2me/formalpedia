-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_pureX_coefficient
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.pureX_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:26:27.940209+00:00
-- url     : https://prove2.me/theorems/b00ad1b5-4cd9-4434-bcfc-7bfa6ee35a8e
-- title:
--   BDL26 History Logical Residual: pure X coefficient
-- statement:
--   The BDL26 History Logical Residual construction uses the pure X coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L202-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L202-L210

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.pureX_coefficient (r : Nat) (v : FC.Cocycle S r) :
    BDL26LogicalQubitPreservation.logicalEquiv S r
        (BDL26LogicalQubitPreservation.logicalClass S r (pureX S r v)) =
      FC.finiteH1Equiv S r (FC.classOf S r v) := by sorry
