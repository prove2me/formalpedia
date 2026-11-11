-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_class_eq_iff_boundary
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.class_eq_iff_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:08:47.274978+00:00
-- url     : https://prove2.me/theorems/00b87c45-0387-4d0e-b42e-8f8607e0454e
-- title:
--   BDL26 History Logical Residual: class eq iff boundary
-- statement:
--   The BDL26 History Logical Residual construction uses the class eq iff boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L160-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L160-L173

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.class_eq_iff_boundary (r : Nat) (v w : FC.Cocycle S r) :
    FC.classOf S r v = FC.classOf S r w ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val-w.val := by sorry
