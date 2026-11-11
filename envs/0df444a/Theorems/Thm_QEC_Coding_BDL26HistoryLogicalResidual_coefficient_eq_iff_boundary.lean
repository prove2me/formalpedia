-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_eq_iff_boundary
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.coefficient_eq_iff_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:05:31.974309+00:00
-- url     : https://prove2.me/theorems/ac0b5a65-8169-417e-9c4c-030cdbaa5177
-- title:
--   BDL26 History Logical Residual: coefficient eq iff boundary
-- statement:
--   The BDL26 History Logical Residual construction uses the coefficient eq iff boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L175-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L175-L183

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.coefficient_eq_iff_boundary (r : Nat) (v w : FC.Cocycle S r) :
    FC.finiteH1Equiv S r (FC.classOf S r v) = FC.finiteH1Equiv S r (FC.classOf S r w) ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val-w.val := by sorry
