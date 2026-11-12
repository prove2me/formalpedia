-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_successProbability
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:59:30.211301+00:00
-- url     : https://prove2.me/theorems/4d8a95ab-c8c0-4010-8654-face9d7782af
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Run success Probability
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Physical Protocol Run success Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean#L183-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean#L183-L198

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_successProbability
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalProtocolRun
        h hdegree epsilon z q hz rhoUnit).successProbability =
      decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput m w z q hz epsilon
          rhoUnit) := by sorry
