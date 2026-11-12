-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolOutcomeFailureMass_eq_shortageMass
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolOutcomeFailureMass_eq_shortageMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:17.191647+00:00
-- url     : https://prove2.me/theorems/eb9449a2-834d-4857-a6e5-5527c34894c2
-- title:
--   HH18 Parameterized: decoded Retry Pool Outcome Failure Mass eq shortage Mass
-- statement:
--   The observed failure mass of one retry-pool outcome is exactly its
--   existing shortage mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L45-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L45-L66

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolOutcomeFailureMass_eq_shortageMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts =>
          PUnit => decodedRetryPoolOutcomeEnough attempts required outcome ≠ true),
      (decodedRetryPoolInstrument h hdegree attempts required).bornWeight outcome rho) =
      decodedRetryPoolShortageMass h hdegree attempts required rho := by sorry
