-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRecordPreparationChannel_mapDensity_product
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRecordPreparationChannel_mapDensity_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:54:43.513813+00:00
-- url     : https://prove2.me/theorems/88bb8bf1-5f43-4007-8470-ea9e7e5d96b5
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Record Preparation Channel map Density product
-- statement:
--   On a genuine product of accepted parent blocks, the physical record
--   preparation remains a genuine product of the corresponding blockwise record
--   densities.  The channel itself is defined on arbitrary, possibly correlated,
--   source registers; only this evaluation theorem uses the accepted-product
--   shape.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L139-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L139-L157

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRecordPreparationChannel_mapDensity_product
    (m w z q : Nat) (stage : Fin z)
    (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (LogicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorRecordPreparationChannel m w z q stage).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerRegisterProductDensity (LogicalSite m w)
        ((decodedRetryPoolQubitRegisterSitewiseChannel
          decodedRetryPoolSuccessorOneQubitRecordChannel
          (LogicalSite m w)).mapDensity rho)
        rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage) := by sorry
