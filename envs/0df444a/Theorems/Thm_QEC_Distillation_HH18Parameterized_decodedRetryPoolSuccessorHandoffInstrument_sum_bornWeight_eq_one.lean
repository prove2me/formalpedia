-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorHandoffInstrument_sum_bornWeight_eq_one
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:39:26.229375+00:00
-- url     : https://prove2.me/theorems/d352e8da-ddb0-42f0-b43d-66c397bd3a5d
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Handoff Instrument sum born Weight eq one
-- statement:
--   Every density input has normalized total observable Born mass under the
--   complete current-pool-to-successor physical handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean#L120-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean#L120-L130

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))) :
    ∑ outcome,
        (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).bornWeight
          outcome rho = 1 := by sorry
