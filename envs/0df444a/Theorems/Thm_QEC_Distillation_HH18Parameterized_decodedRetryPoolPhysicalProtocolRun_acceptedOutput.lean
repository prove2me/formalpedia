-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_acceptedOutput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:00:20.210526+00:00
-- url     : https://prove2.me/theorems/c5c7ba61-c172-43e0-89b4-6c6336a6a2e7
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Run accepted Output
-- statement:
--   The run's accepted conditional density is exactly the normalized accepted
--   branch of the same binary-coarsened physical instrument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean#L202-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean#L202-L220

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_acceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalProtocolRun
      h hdegree epsilon z q hz rhoUnit).acceptedOutput =
      binaryCoarsenCompletion
        (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
        (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
          rhoUnit)
        (decodedRetryPoolPhysicalProtocolFallback m w z q hz) .accepted := by sorry
