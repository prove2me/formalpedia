-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_tensorPowerHistoryAll_eq_true_iff
-- name    : QEC.Distillation.HH18Parameterized.tensorPowerHistoryAll_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:58:27.903864+00:00
-- url     : https://prove2.me/theorems/6deb431e-fc0e-43ad-a0e6-5f6e2ba965cb
-- title:
--   HH18 Parameterized: tensor Power History All eq true iff
-- statement:
--   The recursive Boolean conjunction holds exactly when the predicate holds
--   at every literal tensor coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L35-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L35-L65

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.tensorPowerHistoryAll_eq_true_iff {alpha : Type*}
    (predicate : alpha -> Bool) :
    ∀ (attempts : Nat) (history : tensorPowerHistory alpha attempts),
      tensorPowerHistoryAll predicate attempts history = true ↔
        ∀ trial : Fin attempts,
          predicate (tensorPowerHistoryAt alpha attempts history trial) = true := by sorry
