-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_three_quarters_le
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_three_quarters_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:29:27.086279+00:00
-- url     : https://prove2.me/theorems/6d2eaee1-24bc-4bc8-be21-ef3dd1411ff3
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Success Mass noisy Root three quarters le
-- statement:
--   In the source-derived pooling domain, the genuine complete physical
--   protocol succeeds with Born mass at least three quarters, uniformly at every
--   positive finite depth and terminal batch size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessLowerBound.lean#L94-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessLowerBound.lean#L94-L113

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageFailurePathBound
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_three_quarters_le
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (3 / 4 : Real) ≤
      decodedRetryPoolPhysicalProtocolSuccessMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by sorry
